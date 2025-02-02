from re import I
from sample import Trace
from sketch import Sketch
from z3 import *
import pandas as pd

def pretty_print_dic_list(dic_list):
    """ Prints a list of dictionaries in a nice way

        Parameters
        ----------
        dic_list : list (of dictionaries)
            list to be printed
    """

    for dic in dic_list:
        print(dic)
# ---------------------------------------------------------------------------------------------------


def pretty_print_sample(sample):
    """ Prints a sample in a more readable way

        Parameters
        ----------
        sample : Sample
            sample to be printed
    """

    for p in sample.positive:
        print(p)
    print('----------')
    for n in sample.negative:
        print(n)
# ---------------------------------------------------------------------------------------------------


def build_suffix(word, pos):
    """ Constructs and returns the suffix of an ultimately periodic word as an ultimately periodic word.

        Parameters
        ----------
        word : Trace
            An ultimately periodic word in its finite representation (u v^{\omega})
        pos : int
            The starting position of the suffix in word
    """

    if pos <= word.lasso_start:
        suffix = Trace(word.vector[pos:], word.lasso_start-pos)
    else:
        lasso = word.vector[pos:] + word.vector[word.lasso_start:pos]
        suffix = Trace(lasso, 0)

    return suffix
# ---------------------------------------------------------------------------------------------------


def equal(word_1, word_2):
    """ Checks whether two ultimately periodic words are equal by unrolling them
        to a certain length (determined by the words)

        Parameters
        ----------
        word_1 : Trace

        word_2 : Trace
    """

    if word_2.lasso_start > word_1.lasso_start:     # u_2 > u_1
        return equal(word_2, word_1)

    else:
        abs_u1 = word_1.lasso_start
        abs_v2 = len(word_2.lasso)
        lcm = leastCommonMultiple(len(word_1.lasso), len(word_2.lasso))
        size = abs_u1 + abs_v2 + lcm

        if unroll(word_1.prefix, word_1.lasso, size) == unroll(word_2.prefix, word_2.lasso, size):
            return True
        else:
            return False
# ---------------------------------------------------------------------------------------------------


def is_true_suffix_of(word_1, word_2):
    """ Checks whether a word is a true suffix of another word (i.e., it is a suffix but not equal).
        It then returns the position at which the suffix starts in the original word.

        Parameters
        ----------
        word_1 : Trace
            Original word which is checked to contain word_"

        word_2 : Trace
            Word which is checked to be a true suffix of word_1
    """

    for i in range(1, word_2.length):
        if equal(word_1, build_suffix(word_2, i)):
            return True, i

    return False, -1
# ---------------------------------------------------------------------------------------------------


def unroll(finitePart, lassoPart, length):
    """ Unrolls an ultimately periodic word up to the given length

        Parameters
        ----------
        finitePart : string
            Finite part of the ultimately periodic word
        lassoPart : string
            Lasso part of the ultimately periodic word
        length : int
            Length to which the word is unrolled
    """

    result = copy.copy(finitePart)
    while len(result) < length:
        result += lassoPart
    return result[:length]
# ---------------------------------------------------------------------------------------------------


def leastCommonMultiple(a, b):
    """ Calculates the least common multiple of a and b

        Parameters
        ----------
        a : int
        b : int
    """
    return abs(a * b) // math.gcd(a, b)
# ---------------------------------------------------------------------------------------------------


def reduce_sample(sample):
    """ Reduces the representation of a sample to the minimal representation.
        This includes:
            - Removing duplicates in the lasso (e.g., 'abab' is reduced to 'ab')
            - Removing redundant information in the finite part (e.g., ab{aab} is reduced to {aba}
              where {} indicates the lasso)

        Parameters
        ----------
        sample : Sample
            Sample to be reduced
    """
    traces = sample.positive + sample.negative

    for idx, trace in enumerate(traces):
        # reduce lasso (remove multiple loops)
        for loop_length in range(1, int(trace.lasso_length/2)+1):
            if trace.lasso_length % loop_length == 0:       # length is dividable by l
                multiple = True
                for j in range(loop_length, trace.lasso_length):
                    i = j % loop_length

                    if trace.lasso[i] != trace.lasso[j]:
                        multiple = False
                        break
                if multiple:
                    trace.lasso = trace.lasso[:loop_length]
                    trace.lasso_length = loop_length
                    trace.vector = trace.prefix + trace.lasso
                    trace.length = trace.prefix_length + trace.lasso_length
                    break

        # reduce prefix (shift lasso if possible)
        prefix_pos = trace.prefix_length-1
        while prefix_pos >= 0:
            if trace.prefix[-1] == trace.lasso[-1]:
                trace.lasso = [trace.lasso[-1]] + trace.lasso[:-1]
                trace.lasso_start -= 1
                trace.prefix = trace.prefix[:-1]
                trace.prefix_length -= 1
                trace.vector = trace.prefix + trace.lasso
                trace.length = trace.prefix_length + trace.lasso_length
                prefix_pos -= 1
            else:
                break
    
    # for debugging
    # pretty_print_sample(sample)
# ---------------------------------------------------------------------------------------------------


def suc_1(prefix, lasso, pos):
    """ Computes the successor (i.e., its position) of a suffix in the suffix heuristic

        Note: This is pos + 1 except at the end of the lasso

        Parameters
        ----------
        prefix : string
            Finite prefix of the suffix
        lasso : string
            Lasso of the suffix
        pos : int
            Position for which the successor is supposed to be computed
    """

    word = Trace(prefix + lasso, len(prefix))
    return word.nextPos(pos)
# ---------------------------------------------------------------------------------------------------


def suc_2(sample_entry, pos):
    """ Computes the successor (i.e., its position) of a prefix in the suffix heuristic

        Note: This successor may be in the suffix referenced by the sample_entry

        Parameters
        ----------
        sample_entry : Dictionary
            Representation of the prefix in the suffix heuristic
        pos : int
            Position in the prefix for which the successor is supposed to be computed
    """

    if pos < len(sample_entry["prefix"]) - 1:
        return sample_entry["id"], pos+1
    else:
        return sample_entry["sid"], sample_entry["startpos"]
# ---------------------------------------------------------------------------------------------------


def FUT_1(prefix, lasso, pos):
    """ Computes the set of all successors (i.e., their position) of a suffix in the suffix heuristic

        Parameters
        ----------
        prefix : string
            Finite prefix of the suffix
        lasso : string
            Lasso of the suffix
        pos : int
            Position for which the set of successors is supposed to be computed
    """

    word = Trace(prefix + lasso, len(prefix))
    return word.futurePos(pos)
# ---------------------------------------------------------------------------------------------------


def FUT_2(sample_entry, pos, suffix_entry):
    """ Computes the set of successors (i.e., their position) of a prefix in the suffix heuristic

        Note: These successors may be in the suffix referenced by the sample_entry

        Parameters
        ----------
        sample_entry : Dictionary
            Representation of the prefix in the suffix heuristic
        pos : int
            Position in the prefix for which the successor is supposed to be computed
        suffix_entry : Dictionary
            Entry of the suffix_table referenced by the prefix
    """

    future_positions = []

    for pos_p in range(pos, len(sample_entry["prefix"])):
        future_positions.append((sample_entry["id"], pos_p))

    for f in FUT_1(suffix_entry["u"], suffix_entry["v"], sample_entry["startpos"]):
        future_positions.append((suffix_entry["sid"], f))

    return future_positions
# ---------------------------------------------------------------------------------------------------


def BET_1(prefix, lasso, pos_1, pos_2):
    """ Computes the set of all positions of a suffix in the suffix heuristic between the given positions
        (including the starting position and excluding the end position)

        Parameters
        ----------
        prefix : string
            Finite prefix of the suffix
        lasso : string
            Lasso of the suffix
        pos_1 : int
            Starting position
        pos_2 : int
            End position
    """

    word = Trace(prefix + lasso, len(prefix))
    return word.auxiliaryPos(pos_1, pos_2)
# ---------------------------------------------------------------------------------------------------


def BET_2(id_1, pos_1, id_2, pos_2, start_pos, prefix_length):
    """ Computes the set of all positions of a prefix in the suffix heuristic between the given positions
        (including the starting position and excluding the end position)

        Note: Since the end position can be in the suffix referenced by the entry of the prefix we compare the ID's
        of the two words to check whether this is the case or not

        Parameters
        ----------
        id_1 : string
            ID of the prefix
        id_2 : string
            ID of the word which contains the end position (this is either the same as id_1 or
            references an entry in the suffix_table
        pos_1 : int
            Starting position
        pos_2 : int
            End position
        start_pos : int
            Position in the suffix at which the prefix continues
        prefix_length : int
            Length of the prefix
    """

    between_positions = []

    if str(id_1) == str(id_2):
        for k in range(pos_1, pos_2):
            between_positions.append((id_1, k))

    else:
        for k in range(pos_1, prefix_length):
            between_positions.append((id_1, k))

        for k in range(start_pos, pos_2):
            between_positions.append((id_2, k))

    return between_positions
# ---------------------------------------------------------------------------------------------------


def new_table(sample):
    
    traces = sample.positive + sample.negative

    #Create an initial table with duplicates allowed
    new_table = []  # table of dictionaries{id,u,v,next_id}
    suffix_id=0     # track suffixes to create IDs
    id_fp=0         # variable that sums up the length of each trace added to track first position of each suffix

    for trace_id, trace in enumerate(traces):
        for i in range(trace.length):            
            suffix = build_suffix(trace, i)
            next_id = suffix_id + 1 if i != trace.length - 1 else id_fp + trace.lasso_start
            if trace_id < len(sample.positive) and i == 0:
                type_id=1
            elif trace_id >= len(sample.positive) and i == 0:
                type_id=-1
            else:
                type_id=0
            sample_entry = {
                 'id': suffix_id,                       
                 'u': suffix.prefix,
                 'v': suffix.lasso, 
                 'next_id': next_id,
                 'type':type_id
            }
            suffix_id += 1
            if i == trace.length-1:
                id_fp += trace.length
            new_table.append(sample_entry)

    #Update the next ID and find duplicate rows to delete
    indices_to_delete = set()

    for i, d in enumerate(new_table):
        u_value = tuple(d["u"])
        v_value = tuple(d["v"])
        #j are previous rows which are compared with i
        for j in range(0,i):
            if tuple(new_table[j]["u"]) == u_value and tuple(new_table[j]["v"]) == v_value:
                new_table[i-1]["next_id"] = j
                indices_to_delete.add(i)
                if new_table[i]['type'] == 1:
                    new_table[j]['type'] = 1
                if new_table[i]['type'] == -1:
                    new_table[j]['type'] = -1
                break
       
    # Remove duplicate entries
    for index in sorted(indices_to_delete, reverse=True):
        del new_table[index]
    
    #Post-processing fill the gaps
    # Create a dictionary to map old IDs to new IDs
    id_mapping = {}
    new_id = 0

    # Iterate and create the ID mapping
    for item in new_table:
        old_id = item['id']
        id_mapping[old_id] = new_id
        new_id += 1

    # Iterate and update 'id' and 'next_id' values
    for item in new_table:
        item['id'] = id_mapping[item['id']]
        item['next_id'] = id_mapping[item['next_id']]

    return new_table


def new_table_bmc(ntable):
    for row in ntable:
        if row['next_id'] <= row['id'] and row['id'] in future_positions(ntable, row['next_id']):
            row['bmc'] = 0
        else:
            row['bmc'] = 1

    return ntable


def future_positions(sample_table, k):
    #obtain the mapping of id and next_id
    mapping={}
    for row in sample_table:
        sample_id=row['id']
        mapping[sample_id]=()
        next_id=row['next_id']
        mapping[sample_id]=next_id
    
    future_position={}
    for row in sample_table:
        next2=[]
        sample_id=row['id']
        next2.append(sample_id)
        future_position[sample_id]=[]
        next1=mapping[sample_id]
        while next1 not in next2:
            next2.append(next1)
            sample_i=next1
            next1=mapping[sample_i]
        future_position[sample_id]=next2

    return future_position[k]


def BET_POS(sample_table, j, f):
    fut=future_positions(sample_table, j)
    between_positions = []
    for i in fut:
        if i == f:
            break
        else:
            between_positions.append(i) 
    
    return between_positions


def sample_to_tables(sample):
    """ Transforms the given sample into the prefix- and suffix tables for the suffix heuristic

        Parameters
        ----------
        sample : Sample
            Sample to be transformed
    """

    size = sample.num_positives + sample.num_negatives
    traces = sample.positive + sample.negative

    # initialize variables
    sample_table = []  # table of dictionaries{id,prefix,sid,startpos}
    suffix_table = []  # table of dictionaries{sid,u,v,list}

    reference_table = [None] * size  # maps id of example to entry in sample_table
    suffix_counter = 0  # keeps track of the number of suffixes in suffix_table (to get new sid)
    sample_counter = 0  # keeps track of the number of samples in sample_table (to set reference table)

    for xid, x in enumerate(traces):
        has_suffix_at_all = False

        for offset, y in enumerate(traces[xid + 1:]):
            yid = xid + 1 + offset
            has_common_suffix = False
            common_suffix = None
            x_suffix_start = -1
            y_suffix_start = -1

            # search for common suffix
            for i in range(x.length):
                suffix_1 = build_suffix(x, i)
                for j in range(y.length):
                    suffix_2 = build_suffix(y, j)

                    if equal(suffix_1, suffix_2):
                        has_common_suffix = True
                        common_suffix = suffix_1
                        x_suffix_start = i
                        y_suffix_start = j
                        break

                if has_common_suffix:
                    break

            # Common suffix was found, check reference-table to see in which case we are
            if has_common_suffix:
                has_suffix_at_all = True

                # case 1:
                if reference_table[xid] is None and reference_table[yid] is None:
                    sample_entry_x = {
                        "id": xid,
                        "prefix": x.vector[:x_suffix_start],
                        "sid": 's' + str(suffix_counter),
                        "startpos": 0
                    }
                    sample_table.append(sample_entry_x)
                    reference_table[xid] = sample_counter
                    sample_counter += 1

                    sample_entry_y = {
                        "id": yid,
                        "prefix": y.vector[:y_suffix_start],
                        "sid": 's' + str(suffix_counter),
                        "startpos": 0
                    }
                    sample_table.append(sample_entry_y)
                    reference_table[yid] = sample_counter
                    sample_counter += 1

                    suffix_entry = {
                        "sid": 's' + str(suffix_counter),
                        "u": common_suffix.prefix,
                        "v": common_suffix.lasso,
                        "list": [xid, yid]
                    }
                    suffix_table.append(suffix_entry)
                    suffix_counter += 1
                    
                
                # case 2:
                elif reference_table[xid] is not None and reference_table[yid] is None:
                    u = suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["u"]
                    v = suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["v"]
                    entry = Trace(u + v, len(u))

                    # case 2.1
                    if equal(common_suffix, entry):
                        sample_entry_y = {
                            "id": yid,
                            "prefix": y.vector[:y_suffix_start],
                            "sid": sample_table[reference_table[xid]]["sid"],
                            "startpos": 0
                        }
                        sample_table.append(sample_entry_y)
                        reference_table[yid] = sample_counter
                        sample_counter += 1

                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["list"].append(yid)

                    # case 2.2
                    c_suffix_of_e, pos = is_true_suffix_of(common_suffix, entry)
                    if c_suffix_of_e:
                        sample_entry_y = {
                            "id": yid,
                            "prefix": y.vector[:y_suffix_start],
                            "sid": sample_table[reference_table[xid]]["sid"],
                            "startpos": pos
                        }
                        sample_table.append(sample_entry_y)
                        reference_table[yid] = sample_counter
                        sample_counter += 1

                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["list"].append(yid)

                    # case 2.3
                    e_suffix_of_c, pos = is_true_suffix_of(entry, common_suffix)
                    if e_suffix_of_c:
                        additional_size = pos
                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["u"] = common_suffix.prefix
                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["v"] = common_suffix.lasso

                        for lid in suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["list"]:
                            sample_table[reference_table[lid]]["startpos"] += additional_size

                        sample_table[reference_table[xid]]["pre"] = x.vector[:x_suffix_start]
                        sample_table[reference_table[xid]]["startpos"] = 0

                        sample_entry_y = {
                            "id": yid,
                            "prefix": y.vector[:y_suffix_start],
                            "sid": sample_table[reference_table[xid]]["sid"],
                            "startpos": 0
                        }
                        sample_table.append(sample_entry_y)
                        reference_table[yid] = sample_counter
                        sample_counter += 1

                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["list"].append(yid)

                # case 3:
                elif reference_table[xid] is None and reference_table[yid] is not None:
                    print('ERROR')
                    exit(1)

                # case 4:
                elif reference_table[xid] is not None and reference_table[yid] is not None:
                    u = suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["u"]
                    v = suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["v"]
                    entry = Trace(u + v, len(u))

                    # Compare entry 1 and common_suffix
                    e_suffix_of_c, pos = is_true_suffix_of(entry, common_suffix)

                    if e_suffix_of_c:
                        additional_size = pos
                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["u"] = common_suffix.prefix
                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["v"] = common_suffix.lasso

                        for lid in suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["list"]:
                            sample_table[reference_table[lid]]["startpos"] += additional_size

                        sample_table[reference_table[xid]]["prefix"] = x.vector[:x_suffix_start]
                        sample_table[reference_table[xid]]["startpos"] = 0

                        sample_table[reference_table[yid]]["prefix"] = y.vector[:y_suffix_start]
                        sample_table[reference_table[yid]]["startpos"] = 0

        # case 5
        if not has_suffix_at_all and reference_table[xid] is None:
            sample_entry = {
                "id": xid,
                "prefix": [],
                "sid": 's' + str(suffix_counter),
                "startpos": 0
            }
            sample_table.append(sample_entry)
            reference_table[xid] = sample_counter
            sample_counter += 1

            suffix_entry = {
                "sid": 's' + str(suffix_counter),
                "u": x.prefix,
                "v": x.lasso,
                "list": [xid]
            }
            suffix_table.append(suffix_entry)
            suffix_counter += 1

    # Postprocessing of the Construction of the 2 tables
    for zid, z in enumerate(sample_table):
        u = suffix_table[int(z["sid"][1:])]["u"]
        v = suffix_table[int(z["sid"][1:])]["v"]
        entry = Trace(u + v, len(u))

        for i in range(len(z["prefix"])):
            u_i = z["prefix"][i:] + u
            v_i = v
            word_i = Trace(u_i + v_i, len(u_i))

            z_from_i_suffix_of_entry, pos = is_true_suffix_of(word_i, entry)
            if z_from_i_suffix_of_entry:
                z["prefix"] = z["prefix"][:i]
                z["startpos"] = pos

    return sample_table, suffix_table
# ---------------------------------------------------------------------------------------------------


def construct_Sketch_from_Model(model, alphabet, id, number_of_nodes):
    """ Recursively constructs a Sketch induced by the given model

        Parameters
        ----------
        model : Z3.model
            Model satisfying the set of constraints
        alphabet : List
            The alphabet of the sample, i.e, a list of all symbols occurring in the sample
        id : int
            The ID of the root node
        number_of_nodes : int
            The size for which a satisfying model was found
    """

    sketch = Sketch()
    sketch.identifier = id

    leaf = [ap for ap in alphabet if z3.is_true(model[z3.Bool('x_%s_%s' % (id, ap))])]
    unary = [op for op in ['!', 'X', 'G', 'F'] if z3.is_true(model[z3.Bool('x_%s_%s' % (id, op))])]
    binary = [op for op in ['&', 'v', '->', 'U'] if z3.is_true(model[z3.Bool('x_%s_%s' % (id, op))])]

    if len(leaf) > 0:
        ap = leaf[0]
        sketch.label = ap
        sketch.left = None
        sketch.right = None

    elif len(unary) > 0:
        op = unary[0]
        sketch.label = op

        lchild = [lid for lid in range(id + 1, number_of_nodes) if z3.is_true(model[z3.Bool('l_%s_%s' % (id, lid))])][0]
        sketch.left = construct_Sketch_from_Model(model, alphabet, lchild, number_of_nodes)

        sketch.right = None

    elif len(binary) > 0:
        op = binary[0]
        sketch.label = op

        lchild = [lid for lid in range(id + 1, number_of_nodes) if z3.is_true(model[z3.Bool('l_%s_%s' % (id, lid))])][0]
        sketch.left = construct_Sketch_from_Model(model, alphabet, lchild, number_of_nodes)

        rchild = [rid for rid in range(id + 1, number_of_nodes) if z3.is_true(model[z3.Bool('r_%s_%s' % (id, rid))])][0]
        sketch.right = construct_Sketch_from_Model(model, alphabet, rchild, number_of_nodes)

    return sketch
# ---------------------------------------------------------------------------------------------------


def construct_Sketch_from_Model_cycle_free(rootid, model, alphabet, identifier_list):
    """ Recursively constructs a Sketch induced by the given model but for the cycle free approach
        If node already exists this one is used instead

        Parameters
        ----------
        model : Z3.model
            Model satisfying the set of constraints
        alphabet : List
            The alphabet of the sample, i.e, a list of all symbols occurring in the sample
        rootid : int
            The ID of the root node
        identifier_list : List
            The list of ID's for which a solution was found (due to renaming this may not be the list [1, ..., n])
    """

    sketch_list = []
    labels = alphabet + ['!', 'X', 'G', 'F', '&', 'v', '->', 'U']

    for id in identifier_list:
        label = [label for label in labels if is_true(model[Bool('x_%s_%s' % (id, label))])][0]

        sketch = Sketch()
        sketch.identifier = id
        sketch.label = label

        sketch_list.append(sketch)

    for sketch in sketch_list:
        id = sketch.identifier

        if sketch.label in ['!', 'X', 'G', 'F']:
            left = [pos for pos in identifier_list if is_true(model[Bool('l_%s_%s' % (id, pos))])][0]
            sketch.left = sketch_list[identifier_list.index(left)]

        elif sketch.label in ['&', 'v', '->', 'U']:
            left = [pos for pos in identifier_list if is_true(model[Bool('l_%s_%s' % (id, pos))])][0]
            sketch.left = sketch_list[identifier_list.index(left)]

            right = [pos for pos in identifier_list if is_true(model[Bool('r_%s_%s' % (id, pos))])][0]
            sketch.right = sketch_list[identifier_list.index(right)]

    return sketch_list[identifier_list.index(rootid)]
# ---------------------------------------------------------------------------------------------------

def to_dimacs(clauses):
    # Remove whitespace and empty lines 
    clauses = [clause.strip() for clause in clauses if clause.strip() != ""]

    # Create a mapping to assign unique IDs to variables
    variable_ids = {}
    next_variable_id = 1

    # Create a list to store CNF clauses
    cnf_clauses = []

    for clause in clauses:
        literals = clause.split(', ')
        cnf_clause = []

        for literal in literals:
            # Extract variable and check for negation
            variable = literal.strip('()Not ')
            is_negation = literal.startswith('Not')

            # assign unique ID to variable if not seen before
            if variable not in variable_ids:
                variable_ids[variable] = next_variable_id
                next_variable_id += 1

            variable_id = variable_ids[variable]
            # convert to CNF literal format
            cnf_literal = -variable_id if is_negation else variable_id
            cnf_clause.append(cnf_literal)

        # Add 0 to end the clause
        cnf_clause.append(0)  
        cnf_clauses.append(cnf_clause)

    # Construct the DIMACS string
    dimacs_string = "p cnf {} {}\n".format(len(variable_ids), len(cnf_clauses))
    for clause in cnf_clauses:
        dimacs_string += " ".join(map(str, clause)) + "\n"

    return dimacs_string

# -----------------------------------------------------------------------------------------------------