from z3 import *
from Constraints import semanticConstraints, consistencyConstraints, placeholderConstraints, suffixConstraints
from helping_functions import construct_Sketch_from_Model, equal, to_dimacs
import global_variables
import os

# import values of global variables
generate_lib = global_variables.generate_lib
print_output = global_variables.print_output
print_model = global_variables.print_model
maximumSize = global_variables.maximumSize
build_solution = global_variables.build_solution


def check_existence_tree(sample, sketch, sample_name):
    """ Checks whether there exists a consistent substitution for the given sketch and sample.
        If build_solution is set to true it also computes and outputs such a solution.
        It uses none of the heuristics.

        Parameters
        ----------
        sample : Sample
            The set of traces for which existence of a solution should be checked

        sketch : Sketch
            The sketch for which existence of a solution should be checked
    """

    s = Solver()

    semanticConstraints(s, sketch, sample)
    consistencyConstraints(s, sketch.identifier, sample)
    placeholderConstraints(s, sketch, sketch.getAllNodes())
    suffixConstraints(s, sketch, sample)

    if s.check() == z3.sat:
        print("SAT")
        if build_solution:
            build_solution_tree(sketch, sample, maximumSize, sample_name)
    else:
        print("UNSAT")
# ---------------------------------------------------------------------------------------------------


def build_solution_tree(sketch, sample, finalSize, sample_name):
    """ For the given sketch and sample it computes and outputs a consistent substitution,
        if one exists resulting in a formula of size smaller finalSize
        It uses none of the heuristics.

        If print_model is set to true it also writes the model to a file 'solution.txt'

        Parameters
        ----------
        sample : Sample
            The set of traces for which a solution should be computed

        sketch : Sketch
            The sketch for which a solution should be computed

        finalSize : int
            An upper bound on the size of the solution
    """

    solver_1 = Solver()

    # change type0 placeholders to highest identifiers in sketch
    sketch.change_identifiers()

    # encode consistency (evaluation at the root must match the type (pos, neg) of trace)
    consistencyConstraints(solver_1, sketch.identifier, sample)

    # encode sketch except type0 placeholders, those are the same as the semantic constraints in the existence check
    semanticConstraints(solver_1, sketch, sample)

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
    traces = sample.positive + sample.negative

    # initialize all type-0 placeholder but the last one (will be a leaf)
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
            for j, trace in enumerate(traces):
                for k in range(len(trace)):
                    if trace.vector[k][sample.letter2pos[ap]] == 1:
                        solver_1.add(
                            Implies(
                                Bool('x_%s_%s' % (id, ap)),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k))
                            )
                        )
                    else:
                        solver_1.add(
                            Implies(
                                Bool('x_%s_%s' % (id, ap)),  # ->
                                Not(Bool('z_%s_%s_%s' % (id, j, k)))
                            )
                        )

        for leftid in range(id + 1, last_node_id):
            # unary operators
            for j, trace in enumerate(traces):
                for k in range(trace.length):
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '!')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                        )
                    )

                    # X
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'X')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'F')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in trace.futurePos(k)
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
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in trace.futurePos(k)
                                ]
                            )
                        )
                    )

            for rightid in range(id + 1, last_node_id):
                # binary operators
                for j, trace in enumerate(traces):
                    for k in range(trace.length):
                        # & (And)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '&')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (rightid, j, k))
                                )
                            )
                        )

                        # | (Or)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, 'v')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (rightid, j, k))
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
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Implies(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (rightid, j, k))
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
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Or(
                                    [
                                        And(
                                            [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                            [
                                                Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                                for k_pp in trace.auxiliaryPos(k, k_p)
                                            ]
                                        )
                                        for k_p in trace.futurePos(k)
                                    ]
                                )
                            )
                        )
# ----------------------------------------
    # start looping
    while num_nodes < finalSize:
        if print_output:
            print('looking for formula of size', num_nodes)

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
                for j, trace in enumerate(traces):
                    for k in range(len(trace)):
                        if trace.vector[k][sample.letter2pos[ap]] == 1:
                            solver_1.add(
                                Implies(
                                    Bool('x_%s_%s' % (id, ap)),  # ->
                                    Bool('z_%s_%s_%s' % (id, j, k))
                                )
                            )
                        else:
                            solver_1.add(
                                Implies(
                                    Bool('x_%s_%s' % (id, ap)),  # ->
                                    Not(Bool('z_%s_%s_%s' % (id, j, k)))
                                )
                            )
# ---------------------------
        # previously last node:
        # need to initialize all Constraints for this node:
        if prev_last_node_id != -1:
            id = prev_last_node_id
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
            # unary operators
            for j, trace in enumerate(traces):
                for k in range(trace.length):
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '!')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                        )
                    )

                    # X
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'X')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'F')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in trace.futurePos(k)
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
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in trace.futurePos(k)
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
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )

                    # | (Or)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'v')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, rightid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
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
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Implies(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
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
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Or(
                                [
                                    And(
                                        [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                            for k_pp in trace.auxiliaryPos(k, k_p)
                                        ]
                                    )
                                    for k_p in trace.futurePos(k)
                                ]
                            )
                        )
                    )
# ---------------------------
        # all other nodes
        # it suffices to add:
        # - the 'at least one' Constraints on the children to solver_2,
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
            for j, trace in enumerate(traces):
                for k in range(trace.length):
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '!')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                        )
                    )

                    # X
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'X')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'F')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in trace.futurePos(k)
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
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in trace.futurePos(k)
                                ]
                            )
                        )
                    )
            # binary operators
            for other_id in range(id+1, last_node_id + 1):
                for j, trace in enumerate(traces):
                    for k in range(trace.length):
                        # new node as left child (or both)
                        leftid = last_node_id
                        # & (And)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '&')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                )
                            )
                        )

                        # | (Or)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, 'v')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (other_id, j, k))
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
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Implies(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (other_id, j, k))
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
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Or(
                                    [
                                        And(
                                            [Bool('z_%s_%s_%s' % (other_id, j, k_p))] +
                                            [
                                                Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                                for k_pp in trace.auxiliaryPos(k, k_p)
                                            ]
                                        )
                                        for k_p in trace.futurePos(k)
                                    ]
                                )
                            )
                        )

                        # new node as right child
                        rightid = last_node_id
                        if other_id != rightid:
                            # & (And)
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, '&')),
                                        Bool('l_%s_%s' % (id, other_id)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, j, k)) ==
                                    And(
                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                        Bool('z_%s_%s_%s' % (rightid, j, k))
                                    )
                                )
                            )

                            # | (Or)
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, 'v')),
                                        Bool('l_%s_%s' % (id, other_id)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, j, k)) ==
                                    Or(
                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                        Bool('z_%s_%s_%s' % (rightid, j, k))
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
                                    Bool('z_%s_%s_%s' % (id, j, k)) ==
                                    Implies(
                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                        Bool('z_%s_%s_%s' % (rightid, j, k))
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
                                    Bool('z_%s_%s_%s' % (id, j, k)) ==
                                    Or(
                                        [
                                            And(
                                                [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                                [
                                                    Bool('z_%s_%s_%s' % (other_id, j, k_pp))
                                                    for k_pp in trace.auxiliaryPos(k, k_p)
                                                ]
                                            )
                                            for k_p in trace.futurePos(k)
                                        ]
                                    )
                                )
                            )
# ---------------------------
        # Construct solver s = s1 + s2
        solver = Solver()
        solver.add(solver_1.assertions())
        solver.add(solver_2.assertions())

        # Create output directory
        output_dir='experiment_results/reports'
        os.makedirs(output_dir, exist_ok=True)

        # create the combined goal for tactic
        g = Goal()
        g.add(solver_1.assertions())
        g.add(solver_2.assertions())

        # tactic reduces the problem into propositional CNF
        tactic = Then('simplify', 'bit-blast', 'tseitin-cnf')
        subgoal = tactic(g)
        assert len(subgoal) == 1

        # Extract clauses and convert to DIMACS format 
        clauses = [str(c) for c in subgoal[0]]   
        #print(clauses)
        dimacs_string = to_dimacs(clauses)

        if solver.check() == z3.sat:
            sat = True
            result='SAT'            
        else:
            sat = False
            result='UNSAT'

        sketch_name = ''.join(['Q' if l == '?' else 'Imp' if l == '>' else 'Or' if l == 'v' else l for l in str(sketch)])

        if generate_lib:
            with open(f'{output_dir}/SMT_{sample_name}_{sketch_name}_{num_nodes}_{result}.smt2', 'w') as f1:
                f1.write(solver.to_smt2())

            with open(f'{output_dir}/DIMACS_{sample_name}_{sketch_name}_{num_nodes}_{result}.dimacs', 'w') as f2:
                f2.write(dimacs_string)    
        
        if sat:
            # construct substitutions from model
            m = solver.model()

            if print_model:
                file = 'solution.txt'
                f = open(file, 'w')
                for var in m:
                    f.write(str(var) + ', ' + str(is_true(m[var])) + '\n')
                f.close()

            typ0_ids = sketch.get_type0Positions()
            typ1_ids = sketch.get_type1Positions()
            typ2_ids = sketch.get_type2Positions()

            # type 1 and 2 can be applied directly by chancing the label
            substitutions = []
            for id in typ1_ids:
                sub = (id, [op for op in ['!', 'X', 'G', 'F'] if z3.is_true(m[z3.Bool('x_%s_%s' % (id, op))])][0])
                substitutions.append(sub)

            for id in typ2_ids:
                sub = (id, [op for op in ['&', 'v', '->', 'U'] if z3.is_true(m[z3.Bool('x_%s_%s' % (id, op))])][0])
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
