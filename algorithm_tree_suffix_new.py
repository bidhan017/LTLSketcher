from z3 import *
from Constraints import semanticConstraints_suffix, consistencyConstraints_suffix, placeholderConstraints
from helping_functions import *
import global_variables
import os
import pandas as pd

# import values of global variables
print_debug = global_variables.print_debug
generate_SMTlib = global_variables.generate_SMTlib
print_output = global_variables.print_output
print_model = global_variables.print_model
maximumSize = global_variables.maximumSize
build_solution = global_variables.build_solution


def check_existence_tree_suffix(sample, sketch, sample_name):
    """ Checks whether there exists a consistent substitution for the given sketch and sample.
        If build_solution is set to true it also computes and outputs such a solution.
        For both it uses the suffix heuristic.

        Parameters
        ----------
        sample : Sample
            The set of traces for which existence of a solution should be checked

        sketch : Sketch
            The sketch for which existence of a solution should be checked
    """
    #To print the reduced traces
    #pretty_print_sample(sample)    
    
    #sample_table, suffix_table = sample_to_tables(sample)
    ntable = new_table(sample)
    #print(f'sketch:{sketch}')
    s = Solver()

    semanticConstraints_suffix(s, sketch, ntable, sample.letter2pos)
    consistencyConstraints_suffix(s, sketch.identifier, ntable)
    placeholderConstraints(s, sketch, sketch.getAllNodes())

    if s.check() == z3.sat:
        print("SAT")
        if build_solution:
            build_solution_tree_suffix(sketch, ntable, sample, maximumSize, sample_name)
    else:
        print("UNSAT")
# ---------------------------------------------------------------------------------------------------


def build_solution_tree_suffix(sketch, ntable, sample, finalSize, sample_name):
    """ For the given sketch and sample it computes and outputs a consistent substitution,
        if one exists resulting in a formula of size smaller finalSize
        It uses the suffix heuristic.

        If print_model is set to true it also writes the model to a file 'solution.txt'

        Parameters
        ----------
        sample : Sample
            The set of traces for which a solution should be computed

        sketch : Sketch
            The sketch for which a solution should be computed

        finalSize : int
            An upper bound on the size of the solution

        sample_table : list (of dictionaries{id, prefix, sid, startpos})
            Together with the suffix_table this represents the sample for implementing the suffix heuristic

        suffix_table : list (of dictionaries{sid, u, v, list})
            Together with the sample_table this represents the sample for implementing the suffix heuristic
    """

    solver_1 = Solver()

    # change type0 placeholders to highest identifiers in sketch
    sketch.change_identifiers()

    # encode consistency (evaluation at the root must match the type (pos, neg) of trace)
    consistencyConstraints_suffix(solver_1, sketch.identifier, ntable)


    # encode sketch except type0 placeholders, those are the same as the semantic constraints in the existence check
    semanticConstraints_suffix(solver_1, sketch, ntable, sample.letter2pos)
    
    # encode same evaluation of same placeholders (1/2)
    placeholderConstraints(solver_1, sketch, sketch.getAllNodes())

    num_nodes = sketch.treeSize()
    type_0_nodes = sketch.get_type0Positions()
    additional_nodes = type_0_nodes[:-1]

    if len(type_0_nodes) > 0:
        last_node_id = type_0_nodes[-1]
    else:
        last_node_id = num_nodes - 1       # There is no type-0 placeholder
    prev_last_node_id = -1

    operators = sample.operators
    alphabet = sample.alphabet
    possible_labels = operators + alphabet
# ------------------------------
    # initialize all type-0 placeholder but the last one (will be leaf)
    # consider them as additional nodes
    for id in additional_nodes:
        # at least one label among all labels (operators + alphabet)
        solver_1.add(
            Or(
                [Bool('x_%s_%s' % (id, label)) for label in possible_labels]
            )
        )
        # at most one label among all labels
        # all Combinations of combining two atomic propositions were already added to the solver
        # Therefore, combine each operator with all atomic propositions
        solver_1.add(
            [
                And(
                    [
                        Or(
                            Not(Bool('x_%s_%s' % (id, label))),
                            Not(Bool('x_%s_%s' % (id, label2)))
                        )
                        for label2 in possible_labels[i + 1:]
                    ]
                )
                for i, label in enumerate(possible_labels[:-1])
            ]
        )
        # left child
        # at most one among all but the last node. The last one will be handled in the loop iteration
        solver_1.add(
            [
                And(
                    [
                        Or(
                            Not(Bool('l_%s_%s' % (id, pos_1))),
                            Not(Bool('l_%s_%s' % (id, pos_2)))
                        )
                        for pos_2 in range(pos_1 + 1, last_node_id)
                    ]
                )
                for pos_1 in range(id + 1, last_node_id)
            ]
        )
        # right child
        # at most one among all but the last node. The last one will be handled in the loop iteration
        solver_1.add(
            [
                And(
                    [
                        Or(
                            Not(Bool('r_%s_%s' % (id, pos_1))),
                            Not(Bool('r_%s_%s' % (id, pos_2)))
                        )
                        for pos_2 in range(pos_1 + 1, last_node_id)
                    ]
                )
                for pos_1 in range(id + 1, last_node_id)
            ]
        )
        # Constraints encoding evaluation
        # atomic propositions
        for ap in alphabet:
            for row in ntable:
                j = row["id"]
                trace = row['u'] if row['u'] != [] else row['v']
                if trace[0][sample.letter2pos[ap]] == 1:
                     solver_1.add(
                         Implies(
                             Bool('x_%s_%s' % (id, ap)),  # ->
                             Bool('z_%s_%s' % (id, j))
                         )
                     )
                else:
                     solver_1.add(
                         Implies(
                             Bool('x_%s_%s' % (id, ap)),  # ->
                             Not(Bool('z_%s_%s' % (id, j)))
                         )
                     )


        for leftid in range(id + 1, last_node_id):
            # unary operators
            for row in ntable:
                j = row["id"]

                # ! (Not)
                solver_1.add(
                    Implies(
                        And(
                             Bool('x_%s_%s' % (id, '!')),
                             Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                            Bool('z_%s_%s' % (id, j)) ==
                            Not(Bool('z_%s_%s' % (leftid, j)))
                    )
                )

                # X
                next_id=row['next_id']
                solver_1.add(
                    Implies(
                        And(
                             Bool('x_%s_%s' % (id, 'X')),
                             Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                            Bool('z_%s_%s' % (id, j)) ==
                            Bool('z_%s_%s' % (leftid, next_id))
                    )
                )

                # F
                solver_1.add(
                    Implies(
                         And(
                             Bool('x_%s_%s' % (id, 'F')),
                             Bool('l_%s_%s' % (id, leftid))
                         ),  # ->
                         Bool('z_%s_%s' % (id, j)) ==
                         Or(
                            [
                                Bool('z_%s_%s' % (leftid, f))
                                for f in future_positions(ntable, j)
                            ]
                         )
                    )
                )

                # G
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, 'G')),
                            Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        And(
                            [
                               Bool('z_%s_%s' % (leftid, f))
                               for f in future_positions(ntable, j)
                            ]
                        )
                    )
                )

            for rightid in range(id + 1, last_node_id):
                # binary operators
                for row in ntable:
                    j = row["id"]

                    # & (And)
                    solver_1.add(
                        Implies(
                             And(
                                 Bool('x_%s_%s' % (id, '&')),
                                 Bool('l_%s_%s' % (id, leftid)),
                                 Bool('r_%s_%s' % (id, rightid))
                             ),  # ->
                             Bool('z_%s_%s' % (id, j)) ==
                             And(
                                 Bool('z_%s_%s' % (leftid, j)),
                                 Bool('z_%s_%s' % (rightid, j))
                             )
                        )
                    )

                    # | (Or)
                    solver_1.add(
                        Implies(
                            And(
                                    Bool('x_%s_%s' % (id, '|')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                            ),  # ->
                            Bool('z_%s_%s' % (id, j)) ==
                            Or(
                               Bool('z_%s_%s' % (leftid, j)),
                               Bool('z_%s_%s' % (rightid, j))
                            )
                        )
                    )

                    # ->
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '->')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, rightid))
                            ),  # ->
                            Bool('z_%s_%s' % (id, j)) ==
                            Implies(
                                Bool('z_%s_%s' % (leftid, j)),
                                Bool('z_%s_%s' % (rightid, j))
                            )
                        )
                    )

                    # U
                    solver_1.add(
                         Implies(
                             And(
                                 Bool('x_%s_%s' % (id, 'U')),
                                 Bool('l_%s_%s' % (id, leftid)),
                                 Bool('r_%s_%s' % (id, rightid))
                             ),  # ->
                                Bool('z_%s_%s' % (id, j)) ==
                                Or(
                                    [
                                        And(
                                            [Bool('z_%s_%s' % (rightid, f))] +
                                            [
                                                Bool('z_%s_%s' % (leftid, b))
                                                for b in BET_POS(ntable, j, f)
                                            ]
                                        )
                                        for f in future_positions(ntable, j)
                                    ]
                                )
                         )
                    )

# ----------------------------------------
    # start looping

    while num_nodes < finalSize:

        if print_output:
            print('looking for formula of size', num_nodes)
        #print(f'alphabet:{alphabet}') #p
        #print(f'operators:{operators}') #['G', 'F', '!', 'X', '&', '|', 'U', '->']
        
        solver_2 = Solver()
        # ----------------------------------------
        # last node is leaf. Only necessary if there is at least one type-0 placeholder
        if last_node_id != num_nodes - 1:
            id = last_node_id
            # label is atomic proposition
            # at least one
            solver_2.add(
                Or(
                    [Bool('x_%s_%s' % (id, ap)) for ap in alphabet]
                )
            )
            # at most one
            solver_1.add(
                [
                    And(
                        [
                            Or(
                                Not(Bool('x_%s_%s' % (id, ap))),
                                Not(Bool('x_%s_%s' % (id, ap_2)))
                            )
                            for ap_2 in alphabet[i + 1:]
                        ]
                    )
                    for i, ap in enumerate(alphabet)
                ]
            )
            # and no operator
            solver_2.add(
                And(
                    [Not(Bool('x_%s_%s' % (id, op))) for op in operators]
                )
            )
            
            # evaluation for atomic proposition
            for ap in alphabet:
                for row in ntable:
                    j = row["id"]
                    trace = row['u'] if row['u'] != [] else row['v']

                    if trace[0][sample.letter2pos[ap]] == 1:
                          solver_1.add(
                              Implies(
                                 Bool('x_%s_%s' % (id, ap)),  # ->
                                 Bool('z_%s_%s' % (id, j))
                              )
                          )
                    else:
                          solver_1.add(
                              Implies(
                                 Bool('x_%s_%s' % (id, ap)),  # ->
                                 Not(Bool('z_%s_%s' % (id, j)))
                              )
                          )

        # --------------------------
        # previously last node:
        # need to initialize all Constraints for this node:
        if prev_last_node_id != -1:
            id = prev_last_node_id
            # at least one label among all labels (operators + alphabet)
            #print(possible_labels)   #['G', 'F', '!', 'X', '&', '|', 'U', '->', 'p']

            solver_1.add(
                Or(
                    [Bool('x_%s_%s' % (id, label)) for label in possible_labels]
                )
            )

            # at most one label among all labels
            # all Combinations of combining two atomic propositions were already added to the solver
            # Therefore, combine each operator with all atomic propositions
            solver_1.add(
                [
                    And(
                        [
                            Or(
                                Not(Bool('x_%s_%s' % (id, op))),
                                Not(Bool('x_%s_%s' % (id, ap)))
                            )
                            for ap in alphabet
                        ]
                    )
                    for op in operators
                ]
            )

            # additionally, consider each pair of operators
            solver_1.add(
                [
                    And(
                        [
                            Or(
                                Not(Bool('x_%s_%s' % (id, op_1))),
                                Not(Bool('x_%s_%s' % (id, op_2)))
                            )
                            for op_2 in operators[i+1:]
                        ]
                    )
                    for i, op_1 in enumerate(operators)
                ]
            )

            # left child
            # there is only one valid option (requires higher index)
            solver_2.add(
                Bool('l_%s_%s' % (id, last_node_id))
            )

            # right child
            # at least one (with higher index)
            solver_2.add(
                Bool('r_%s_%s' % (id, last_node_id))
            )
            # Constraints encoding evaluation, atomic proposition were already added
            leftid = last_node_id
            rightid = last_node_id

            for row in ntable:
                j = row["id"]

                # ! (Not)
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, '!')),
                            Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        Not(Bool('z_%s_%s' % (leftid, j)))
                    )
                )

                # X
                next_id=row['next_id']
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, 'X')),
                            Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        Bool('z_%s_%s' % (leftid, next_id))
                    )
                )

                # F
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, 'F')),
                            Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        Or(
                            [
                               Bool('z_%s_%s' % (leftid, f))
                               for f in future_positions(ntable, j)
                            ]
                        )
                    )
                )

                # G
                solver_1.add(
                    Implies(
                        And(
                             Bool('x_%s_%s' % (id, 'G')),
                             Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        And(
                             [
                                Bool('z_%s_%s' % (leftid, f))
                                for f in future_positions(ntable, j)
                             ]
                        )
                    )
                )
                
                # & (And)
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, '&')),
                            Bool('l_%s_%s' % (id, leftid)),
                            Bool('r_%s_%s' % (id, rightid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        And(
                            Bool('z_%s_%s' % (leftid, j)),
                            Bool('z_%s_%s' % (rightid, j))
                        )
                    )
                )

                # | (Or)
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, '|')),
                            Bool('l_%s_%s' % (id, leftid)),
                            Bool('r_%s_%s' % (id, rightid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        Or(
                           Bool('z_%s_%s' % (leftid, j)),
                           Bool('z_%s_%s' % (rightid, j))
                        )
                    )
                )

                # ->
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, '->')),
                            Bool('l_%s_%s' % (id, leftid)),
                            Bool('r_%s_%s' % (id, rightid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        Implies(
                            Bool('z_%s_%s' % (leftid, j)),
                            Bool('z_%s_%s' % (rightid, j))
                        )
                    )
                )

                # U
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, 'U')),
                            Bool('l_%s_%s' % (id, leftid)),
                            Bool('r_%s_%s' % (id, rightid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        Or(
                            [
                               And(
                                    [Bool('z_%s_%s' % (rightid, f))] +
                                    [
                                       Bool('z_%s_%s' % (leftid, b))
                                       for b in BET_POS(ntable, j, f)
                                    ]
                               )
                               for f in future_positions(ntable, j)
                            ]
                        )
                    )
                )

# --------------------------------------
        # all other nodes
        # it suffices to add:
        # - the at least one Constraints on the children to solver_2,
        # - the at most one containing the new last node to solver_1
        # - and the evaluation with the new last node as one of the children also to solver_1

        for id in additional_nodes:
            # left child
            # at least one (with higher index)
            solver_2.add(
                Or(
                    [Bool('l_%s_%s' % (id, pos)) for pos in range(id + 1, last_node_id + 1)]
                )
            )
            # at most one
            solver_1.add(
                And(
                    [
                        Or(
                            Not(Bool('l_%s_%s' % (id, last_node_id))),
                            Not(Bool('l_%s_%s' % (id, pos)))
                        )
                        for pos in range(id + 1, last_node_id)
                    ]
                )
            )
            # right child
            # at least one (with higher index)
            solver_2.add(
                Or(
                    [Bool('r_%s_%s' % (id, pos)) for pos in range(id + 1, last_node_id + 1)]
                )
            )
            # at most one
            solver_1.add(
                And(
                    [
                        Or(
                            Not(Bool('r_%s_%s' % (id, last_node_id))),
                            Not(Bool('r_%s_%s' % (id, pos)))
                        )
                        for pos in range(id + 1, last_node_id)
                    ]
                )
            )

            # Constraints encoding evaluation
            # unary operators
            leftid = last_node_id
            for row in ntable:
                j = row["id"]

                # ! (Not)
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, '!')),
                            Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        Not(Bool('z_%s_%s' % (leftid, j)))
                    )
                )

                # X
                next_id=row['next_id']
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, 'X')),
                            Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        Bool('z_%s_%s' % (leftid, next_id))
                    )
                )

                # F
                solver_1.add(
                    Implies(
                        And(
                             Bool('x_%s_%s' % (id, 'F')),
                             Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        Or(
                            [
                               Bool('z_%s_%s' % (leftid, f))
                               for f in future_positions(ntable, j)
                            ]
                        )
                    )
                )

                # G
                solver_1.add(
                    Implies(
                        And(
                            Bool('x_%s_%s' % (id, 'G')),
                            Bool('l_%s_%s' % (id, leftid))
                        ),  # ->
                        Bool('z_%s_%s' % (id, j)) ==
                        And(
                            [
                               Bool('z_%s_%s' % (leftid, f))
                               for f in future_positions(ntable, j)
                            ]
                        )
                    )
                )
 
            # binary operators
            for other_id in range(id+1, last_node_id + 1):
                leftid = last_node_id
                for row in ntable:
                    j = row["id"]

                    # & (And)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '&')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, other_id))
                            ),  # ->
                            Bool('z_%s_%s' % (id, j)) ==
                            And(
                                Bool('z_%s_%s' % (leftid, j)),
                                Bool('z_%s_%s' % (other_id, j))
                            )
                        )
                    )

                    # | (Or)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '|')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, other_id))
                            ),  # ->
                            Bool('z_%s_%s' % (id, j)) ==
                            Or(
                               Bool('z_%s_%s' % (leftid, j)),
                               Bool('z_%s_%s' % (other_id, j))
                            )
                        )
                    )

                    # ->
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '->')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, other_id))
                            ),  # ->
                            Bool('z_%s_%s' % (id, j)) ==
                            Implies(
                                Bool('z_%s_%s' % (leftid, j)),
                                Bool('z_%s_%s' % (other_id, j))
                            )
                        )
                    )

                    # U
                    solver_1.add(
                        Implies(
                            And(
                                 Bool('x_%s_%s' % (id, 'U')),
                                 Bool('l_%s_%s' % (id, leftid)),
                                 Bool('r_%s_%s' % (id, other_id))
                            ),  # ->
                            Bool('z_%s_%s' % (id, j)) ==
                            Or(
                                [
                                   And(
                                        [Bool('z_%s_%s' % (other_id, f))] +
                                        [
                                           Bool('z_%s_%s' % (leftid, b))
                                           for b in BET_POS(ntable, j, f)
                                        ]
                                   )
                                   for f in future_positions(ntable, j)
                                ]
                            )
                        )
                    )

                # ----------
                # new node as right child
                rightid = last_node_id
                if other_id != rightid:
                    for row in ntable:
                        j = row["id"]

                        # & (And)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '&')),
                                    Bool('l_%s_%s' % (id, other_id)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s' % (id, j)) ==
                                And(
                                    Bool('z_%s_%s' % (other_id, j)),
                                    Bool('z_%s_%s' % (rightid, j))
                                )
                            )
                        )

                        # | (Or)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '|')),
                                    Bool('l_%s_%s' % (id, other_id)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s' % (id, j)) ==
                                Or(
                                   Bool('z_%s_%s' % (other_id, j)),
                                   Bool('z_%s_%s' % (rightid, j))
                                )
                            )
                        )

                        # ->
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '->')),
                                    Bool('l_%s_%s' % (id, other_id)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s' % (id, j)) ==
                                Implies(
                                    Bool('z_%s_%s' % (other_id, j)),
                                    Bool('z_%s_%s' % (rightid, j))
                                )
                            )
                        )

                        # U
                        solver_1.add(
                            Implies(
                                And(
                                     Bool('x_%s_%s' % (id, 'U')),
                                     Bool('l_%s_%s' % (id, other_id)),
                                     Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s' % (id, j)) ==
                                Or(
                                    [
                                       And(
                                            [Bool('z_%s_%s' % (rightid, f))] +
                                            [
                                              Bool('z_%s_%s' % (other_id, b))
                                              for b in BET_POS(ntable, j, f)
                                            ]
                                       )
                                       for f in future_positions(ntable, j)
                                    ]
                                )
                            )
                        )
 
# -------------------------------
        # Construct solver s = s1 + s2
        solver = Solver()
        solver.add(solver_1.assertions())
        solver.add(solver_2.assertions())

        ##HERE##
        output_dir='experiment_results/reports'
        os.makedirs(output_dir, exist_ok=True)

        if solver.check() == z3.sat:
            # construct substitutions from model
            m = solver.model()

            if print_model:
                file = 'solution.txt'
                f = open(file, 'w')
                for e in m:
                    f.write(str(e) + ', ' + str(is_true(m[e])) + '\n')
                f.close()

            if generate_SMTlib:
                filename = f'experiment_results/reports/SMT_{sample_name}_sketch_{num_nodes}.smt2'
                with open(filename, mode='w') as f1:
                    f1.write(solver.to_smt2())
                f1.close()

            typ0_ids = sketch.get_type0Positions()
            typ1_ids = sketch.get_type1Positions()
            typ2_ids = sketch.get_type2Positions()

            # type 1 and 2 can be applied directly by chancing the label
            substitutions = []
            for id in typ1_ids:
                sub = (id, [op for op in ['!', 'X', 'G', 'F'] if z3.is_true(m[z3.Bool('x_%s_%s' % (id, op))])][0])
                substitutions.append(sub)

            for id in typ2_ids:
                sub = (id, [op for op in ['&', '|', '->', 'U'] if z3.is_true(m[z3.Bool('x_%s_%s' % (id, op))])][0])
                substitutions.append(sub)

            LTL = sketch.substitute_sketch_type_1_2(substitutions)

            # for type 0 placeholders a new sketch has to be constructed which replaces the placeholder-node
            substitutions = []

            for id in typ0_ids:
                sub = (id, construct_Sketch_from_Model(m, alphabet, id, last_node_id + 1))
                substitutions.append(sub)

            cLTL = LTL.substitute_sketch_type_0(substitutions)
            cLTL.reduce()

            if print_output:
                print(cLTL.prettyPrint(True))
                print(sample.isFormulaConsistent(cLTL))

            break
        else:
            if prev_last_node_id != -1:
                additional_nodes.append(prev_last_node_id)
            if last_node_id != num_nodes - 1:
                prev_last_node_id = last_node_id
                last_node_id += 1
                num_nodes += 1

        if num_nodes == finalSize:
            if print_output:
                print('No solution found up to size', finalSize)
# ---------------------------------------------------------------------------------------------------
