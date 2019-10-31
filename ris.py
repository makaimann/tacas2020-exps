from collections import namedtuple, defaultdict
from pathlib import Path
from typing import Tuple, List, Optional, NamedTuple

from cosa.analyzers.mcsolver import BMCSolver
from cosa.encoders.verilog_yosys import VerilogYosysBtorParser
from cosa.encoders.btor2 import BTOR2Parser
from cosa.representation import HTS, TS
from cosa.utils.formula_mngm import SortingNetwork, substitute, get_free_variables

from pysmt.shortcuts import And, BOOL, BV, BVULE, BVType, EqualsOrIff, Implies, Not, Or, simplify, Solver, Symbol, TRUE
from pysmt.fnode import FNode
from pysmt.rewritings import conjunctive_partition

from por_utils import assume, btor_config, copy_sys, interface, temporal_sys

__all__ = ['reduced_instruction_set', 'read_verilog', 'read_btor']

# hacky -- creating config here
# should have an api command to get a generic config object from CoSA

def test_actions(actions, en):
    '''
    Ensure that actions don't imply eachother
    '''
    s = Solver()

    # assume that action can't occur without being enabled
    for a, e in zip(actions, en):
        s.add_assertion(Implies(a, e))

    # now check that you can run an action with all the others disabled
    other_actions = set(actions)
    for a in actions:
        s.push()
        # remove current action
        other_actions.remove(a)

        # assume this action is enabled but none of the others are
        s.add_assertion(a)
        for oa in other_actions:
            s.add_assertion(Not(oa))

        assert s.check_sat(), \
            ("Expecting actions to not imply eachother but "
             "{} implies one of the other options".format(a))

        # add it back in
        other_actions.add(a)
        s.pop()

def ris_proof_setup(hts, config, generic_interface):
    B = 3
    for a in generic_interface.actions:
        assert a.get_type() == BOOL

    print("++++++++++++ automating reduced instruction set search ++++++++++++++++")
    print("Got HTS:", hts)

    print("----------------- adding assumptions to the HTS definition ----------------")

    # convert to a list, we want it to be ordered now
    data_inputs = generic_interface.data_inputs

    print('Found the following data inputs:\n\t', data_inputs)

    # assume reset is zero
    if generic_interface.rst is not None:
        rst_zero = EqualsOrIff(generic_interface.rst, BV(0, 1))
    else:
        rst_zero = TRUE()
    print("Simple assumption: Hold reset at zero:\n\t", rst_zero)

    # isn't even necessary for simple FIFO without scoreboard (because pointers still end up in same place)
    enabled_conds = And([Implies(a, e) for a, e in zip(generic_interface.actions, generic_interface.ens)])
    print("Add enabled-ness assumptions:\n\t", enabled_conds.serialize(100))

    # create a new transition system to add to the HTS
    ts = TS()
    ts.set_behavior(TRUE(), enabled_conds, rst_zero)
    hts.add_ts(ts)

    # Now the system is ready to be copied
    # Create copy of system
    hts_copy, copy_interface, _, copymap = copy_sys(hts, generic_interface)

    # assume data stays constant
    data_stays_const = And([EqualsOrIff(TS.get_prime(di), di) for di in copy_interface.data_inputs])
    print("Simple assumption: data inputs all remain constant in copy:\n\t", data_stays_const)

    ts = TS()
    ts.set_behavior(TRUE(), data_stays_const, TRUE())
    hts_copy.add_ts(ts)

    # update the main system
    hts_comb = HTS()
    hts_comb.combine(hts)
    hts_comb.combine(hts_copy)

    bmc = BMCSolver(hts_comb, config)
    # union_vars = hts_comb.vars.union(hts_copy.vars)
    bmc._init_at_time(hts_comb.vars, 2)
    invar = hts_comb.single_invar()
    trans = hts_comb.single_trans()
    invar0 = bmc.at_time(invar, 0)
    assume(bmc, invar0, "Assuming invariant at 0")
    unrolled = bmc.unroll(trans, invar, B)
    assume(bmc, unrolled, "Assuming unrolled system")

    timed_actions = defaultdict(list)
    timed_ens     = defaultdict(list)
    timed_data_inputs = defaultdict(list)
    for t in range(B):
        for a in generic_interface.actions:
            timed_actions[t].append(bmc.at_time(a, t))
        for e in generic_interface.ens:
            timed_ens[t].append(bmc.at_time(e, t))
        for di in generic_interface.data_inputs:
            timed_data_inputs[t].append(bmc.at_time(di, t))
        assert len(timed_actions[t]) == len(timed_ens[t])

    copy_timed_actions = defaultdict(list)
    copy_timed_ens    = defaultdict(list)
    copy_timed_data_inputs = defaultdict(list)
    for t in range(B):
        for ca in copy_interface.actions:
            copy_timed_actions[t].append(bmc.at_time(ca, t))
        for e in copy_interface.ens:
            copy_timed_ens[t].append(bmc.at_time(e, t))
        for cdi in copy_interface.data_inputs:
            copy_timed_data_inputs[t].append(bmc.at_time(cdi, t))
        assert len(copy_timed_actions[t]) == len(copy_timed_ens[t])

    # timed_sys_equiv = list()
    # for t in range(B):
    #     timed_sys_equiv.append(bmc.at_time(sys_equiv_output, t))
    sys_equiv_output0 = And([bmc.at_time(EqualsOrIff(sv, substitute(sv, copymap)), 0) for sv in hts.state_vars])
    sys_equiv_output_end = And([EqualsOrIff(bmc.at_time(sv, 1), bmc.at_time(substitute(sv, copymap), 2)) for sv in hts.state_vars])
    timed_sys_equiv = [sys_equiv_output0, sys_equiv_output_end]

    print()
    print('TIMED ACTIONS:')
    for t in timed_actions:
        print("\t{}: {} - en: {}".format(t, timed_actions[t], timed_ens[t]))

    print('COPY TIMED ACTIONS:')
    for t in copy_timed_actions:
        print("\t{}: {} - en: {}".format(t, copy_timed_actions[t], copy_timed_ens[t]))

    print()
    print('TIMED EQUIV OUTPUT:')
    for e in timed_sys_equiv:
        print("\t", e)

    unrolled_sys = temporal_sys(bmc=bmc,
                     timed_actions=timed_actions,
                     timed_ens=timed_ens,
                     timed_data_inputs=timed_data_inputs,
                     copy_timed_actions=copy_timed_actions,
                     copy_timed_ens=copy_timed_ens,
                     copy_timed_data_inputs=copy_timed_data_inputs,
                     timed_sys_equiv=timed_sys_equiv)

    return unrolled_sys

def setup_delay_logic(unrolled_sys:temporal_sys)->Tuple[List[FNode], List[FNode]]:

    # unpack the entire named tuple
    bmc=unrolled_sys.bmc
    timed_actions=unrolled_sys.timed_actions
    timed_ens=unrolled_sys.timed_ens
    timed_data_inputs=unrolled_sys.timed_data_inputs
    copy_timed_actions=unrolled_sys.copy_timed_actions
    copy_timed_ens=unrolled_sys.copy_timed_ens
    copy_timed_data_inputs=unrolled_sys.copy_timed_data_inputs
    timed_sys_equiv=unrolled_sys.timed_sys_equiv

    print("+++++++++++++++++ Setting up delay logic for automated proof +++++++++++++++++++++")

    print()
    # assume they start in the same state
    print("Assuming systems start in the same state:")
    assume(bmc, timed_sys_equiv[0])

    # assume the data starts the same
    print("Assume the data is equivalent")
    for di0, cdi0 in zip(timed_data_inputs[0], copy_timed_data_inputs[0]):
        assume(bmc, EqualsOrIff(di0, cdi0))
    print()

    # Generate delay indicator for each action
    print("Generating delay indicator for each action")
    delay = []
    delay_width = (len(timed_actions[0])-1).bit_length()
    delay_sel = Symbol('delay_sel', BVType(delay_width))
    for i in range(len(timed_actions[0])):
        delay.append(EqualsOrIff(delay_sel, BV(i, delay_width)))

    if len(timed_actions[0]) != 2**delay_width:
        assumption = BVULE(delay_sel, BV(len(timed_actions[0])-1, delay_width))
        assume(bmc, assumption)
    print()

    print("Add assumptions about actions in second and third states:")
    # original system only uses actions in the first state
    for a in timed_actions[1]:
        assume(bmc, Not(a))

    for generic_actions in [timed_actions, copy_timed_actions]:
        # assume that no actions are enabled in the last state (just comparing state now)
        for ta in generic_actions[2]:
            assume(bmc, Not(ta))
    print()

    # Usage
    sn = SortingNetwork.sorting_network(timed_actions[0])
    print("\nSorting Network:\n\t", sn)
    print()

    # assertion that delayed signal is enabled
    delayed_signal_enabled = And([Implies(delay[i], copy_timed_ens[1][i]) for i in range(len(delay))])

    return delay_sel, delay, sn

def simple_delay_strategy(unrolled_sys:temporal_sys, delay:List[FNode], sn:List[FNode], predicates:Optional[List[FNode]]=None, delay_sel:Optional[FNode]=None)->bool:

    if predicates is not None and len(predicates):
        raise ValueError("Simple delay strategy does not support arbitrary predicates")

    # unpack the entire named tuple
    bmc=unrolled_sys.bmc
    timed_actions=unrolled_sys.timed_actions
    timed_ens=unrolled_sys.timed_ens
    timed_data_inputs=unrolled_sys.timed_data_inputs
    copy_timed_actions=unrolled_sys.copy_timed_actions
    copy_timed_ens=unrolled_sys.copy_timed_ens
    copy_timed_data_inputs=unrolled_sys.copy_timed_data_inputs
    timed_sys_equiv=unrolled_sys.timed_sys_equiv

    print("++++++++++++++++++++ Running Simple Delay Strategy +++++++++++++++++++++")
    ################ add assumptions about delay signal ###################
    # if delaying a signal, it must have been enabled
    print("Assume that delayed action must occur in first state in original system")
    for d, a in zip(delay, timed_actions[0]):
        assumption = Implies(d, a)
        assume(bmc, assumption)

    print("Assume that delayed action can't occur in first state in copy")
    for d, ca in zip(delay, copy_timed_actions[0]):
        assume(bmc, Implies(d, Not(ca)))
    print()

    print("Assume that if not delayed, the action and copy of action are equal")
    for d, a, ca in zip(delay, timed_actions[0], copy_timed_actions[0]):
        assume(bmc, Implies(Not(d), EqualsOrIff(a, ca)))
    print()

    # simple delay assumptions
    print("Assume that the delayed action is at time step 1 in the copied system")
    for d, ca in zip(delay, copy_timed_actions[1]):
        assume(bmc, Implies(d, ca))
    print()

    print("Assume that the delayed action is the only action at time 1")
    for d, ca in zip(delay, copy_timed_actions[1]):
        assume(bmc, Implies(Not(d), Not(ca)))
    print()

    # previous bug explanation
    # I had a property like (a -> b) OR (c -> d), which when negated becomes (a AND -b) AND (c AND -d), but a AND c is already unsat in this case so that does NOT work

    # looked like this:
    # full_consequent = Or(Implies(delay[0], And(copy_timed_ens[1][0], timed_sys_equiv[2])),
    #                      Implies(delay[1], And(copy_timed_ens[1][1], timed_sys_equiv[2])))
    # raise RuntimeError("Currently buggy")


    for i in range(1, len(timed_actions[0])):
        print("======= Proving that an action can be delayed for instruction cardinality = {} ======".format(i+1))
        antecedent = sn[i]
        if i < len(timed_actions[0]) - 1:
            # it's exactly i+1 actions enabled
            antecedent = And(antecedent, Not(sn[i+1]))
        prop = Implies(antecedent, timed_sys_equiv[-1])
        assumptions = [Not(prop)]
        res = bmc.solver.solver.solve(assumptions)
        if res:
            model = bmc.solver.solver.get_model()
            print("+++++++++++++++++++++++ Model +++++++++++++++++++++++")
            print(model)
            return False
        else:
            return True

def ceg_strategy(unrolled_sys:temporal_sys, delay:List[FNode], sn:List[FNode], predicates:Optional[List[FNode]]=None,
                 delay_sel:Optional[FNode]=None, monotonic:bool=True, constrain_copy=True)->bool:
    '''
    Counter-example guided strategy

    Options:
    # monotonic       : monotonicity with respect to the original system actions
    #                   when true only consider applied actions from the original system when learning the witness function
    # constrain_copy  : extra guidance for the copy system
    #                   when true add the assumption that actions that don't occur at time 0 in the original
    #                   also don't occur in the copy at time 0
    '''

    if predicates is None:
        predicates = []

    if delay_sel is None:
        print("Auto-detecting delay_sel...")
        delay_sel = get_free_variables(delay[0])
        assert len(delay_sel) == 1
        delay_sel = delay_sel[0]

    # unpack the entire named tuple
    bmc=unrolled_sys.bmc
    timed_actions=unrolled_sys.timed_actions
    timed_ens=unrolled_sys.timed_ens
    timed_data_inputs=unrolled_sys.timed_data_inputs
    copy_timed_actions=unrolled_sys.copy_timed_actions
    copy_timed_ens=unrolled_sys.copy_timed_ens
    copy_timed_data_inputs=unrolled_sys.copy_timed_data_inputs
    timed_sys_equiv=unrolled_sys.timed_sys_equiv

    for i, p in enumerate(predicates):
        predicates[i] = bmc.at_time(p, 0)

    print("++++++++++++++++++++ Running Counter-Example Strategy +++++++++++++++++++++")
    ################ add assumptions about delay signal ###################
    # if delaying a signal, it must have been enabled
    print("Assume that delayed action must occur in first state in original system")
    for d, a in zip(delay, timed_actions[0]):
        assumption = Implies(d, a)
        assume(bmc, assumption)
    print()

    print("Assume that delayed action can't occur in first state in copy")
    for d, ca in zip(delay, copy_timed_actions[0]):
        assume(bmc, Implies(d, Not(ca)))
    print()

    print("Assume that the delayed action is the only action at time 1")
    for d, ca in zip(delay, copy_timed_actions[1]):
        assume(bmc, Implies(Not(d), Not(ca)))
    print()

    if constrain_copy:
        print("Assume that copy can apply options that original did in time 0")
        for a, ca in zip(timed_actions[0], copy_timed_actions[0]):
            assume(bmc, Implies(ca, a))
        print()

    # counter-example guided loop
    model = None
    # property is equivalence at end time
    prop = timed_sys_equiv[-1]
    for i in range(1, len(timed_actions[0])):
        print("======= Proving that an action can be delayed for instruction cardinality = {} ======".format(i+1))
        antecedent = sn[i]
        if i < len(timed_actions[0]) - 1:
            # it's exactly i+1 actions enabled, e.g. don't let it be more
            antecedent = And(antecedent, Not(sn[i+1]))

        res = True

        while res:
            assumptions = [antecedent, Not(prop)]
            res = bmc.solver.solver.solve(assumptions)

            if res:
                model = bmc.solver.solver.get_model()
                witness_antecedent = []
                witness_neg_consequent = []
                complex_instruction = []
                for ta in timed_actions[0]:
                    vta = bmc.solver.solver.get_value(ta).constant_value()
                    if vta:
                        complex_instruction.append(ta)
                        witness_antecedent.append(ta)
                    else:
                        complex_instruction.append(Not(ta))

                if not monotonic:
                    # create shallow copy
                    witness_antecedent = list(complex_instruction)
                    witness_antecedent.append(Not(prop))

                # now add predicates
                for p in predicates:
                    vp = bmc.solver.solver.get_value(p).constant_value()
                    if vp:
                        witness_antecedent.append(p)
                    else:
                        witness_antecedent.append(Not(p))

                # only considering time 0 and only allow delayed action at time 1
                # to be more general, could let the witness constraint range over time 0 and time 1
                for cta in copy_timed_actions[0]:
                    vcta = bmc.solver.solver.get_value(cta).constant_value()
                    if vcta:
                        witness_neg_consequent.append(cta)
                    else:
                        witness_neg_consequent.append(Not(cta))
                vdelay = bmc.solver.solver.get_value(delay_sel)
                witness_neg_consequent.append(EqualsOrIff(delay_sel, vdelay))
                # let it decide whether or not to include the action at time step 1
                # look up the action that's supposed to be delayed
                action = copy_timed_actions[1][vdelay.constant_value()]
                if bmc.solver.solver.get_value(action).constant_value():
                    witness_neg_consequent.append(action)
                else:
                    witness_neg_consequent.append(Not(action))
                witness_constraint = Implies(And(witness_antecedent), Not(And(witness_neg_consequent)))

                print()
                print("Learned witness constraint:")
                assume(bmc, witness_constraint, serialize=100)
                print()

                # check that we haven't over-constrained with the learned witness
                if not bmc.solver.solver.solve([antecedent, And(complex_instruction)]):
                    print("Previous model")
                    print(model)

                    print("Failed with complex instruction:", complex_instruction)
                    raise RuntimeError("Bummer: Over-constrained by witness -- giving up")

            else:
                continue
    return True

def simple_ceg_strategy(unrolled_sys:temporal_sys, delay:List[FNode], sn:List[FNode], predicates:Optional[List[FNode]]=None,
                 delay_sel:Optional[FNode]=None, monotonic:bool=True, constrain_copy=True)->bool:
    '''
    Counter-example guided strategy but with some assumptions. Just tries to find an action to delay

    Options:
    # monotonic       : monotonicity with respect to the original system actions
    #                   when true only consider applied actions from the original system when learning the witness function
    # constrain_copy  : extra guidance for the copy system
    #                   when true add the assumption that actions that don't occur at time 0 in the original
    #                   also don't occur in the copy at time 0
    '''

    if predicates is None:
        predicates = []

    if delay_sel is None:
        print("Auto-detecting delay_sel...")
        delay_sel = get_free_variables(delay[0])
        assert len(delay_sel) == 1
        delay_sel = delay_sel[0]

    # unpack the entire named tuple
    bmc=unrolled_sys.bmc
    timed_actions=unrolled_sys.timed_actions
    timed_ens=unrolled_sys.timed_ens
    timed_data_inputs=unrolled_sys.timed_data_inputs
    copy_timed_actions=unrolled_sys.copy_timed_actions
    copy_timed_ens=unrolled_sys.copy_timed_ens
    copy_timed_data_inputs=unrolled_sys.copy_timed_data_inputs
    timed_sys_equiv=unrolled_sys.timed_sys_equiv

    for i, p in enumerate(predicates):
        predicates[i] = bmc.at_time(p, 0)

    print("++++++++++++++++++++ Running Counter-Example Strategy +++++++++++++++++++++")
    ################ add assumptions about delay signal ###################
    # if delaying a signal, it must have been enabled
    print("Assume that delayed action must occur in first state in original system")
    for d, a in zip(delay, timed_actions[0]):
        assumption = Implies(d, a)
        assume(bmc, assumption)
    print()

    print("Assume that delayed action can't occur in first state in copy")
    for d, ca in zip(delay, copy_timed_actions[0]):
        assume(bmc, Implies(d, Not(ca)))
    print()

    print("Assume that if not delayed, the action and copy of action are equal")
    for d, a, ca in zip(delay, timed_actions[0], copy_timed_actions[0]):
        assume(bmc, Implies(Not(d), EqualsOrIff(a, ca)))
    print()

    print("Assume that the delayed action is at time step 1 in the copied system")
    for d, ca in zip(delay, copy_timed_actions[1]):
        assume(bmc, Implies(d, ca))
    print()

    print("Assume that the delayed action is the only action at time 1")
    for d, ca in zip(delay, copy_timed_actions[1]):
        assume(bmc, Implies(Not(d), Not(ca)))
    print()

    if constrain_copy:
        print("Assume that copy can apply options that original did in time 0")
        for a, ca in zip(timed_actions[0], copy_timed_actions[0]):
            assume(bmc, Implies(ca, a))
        print()

    # counter-example guided loop
    model = None
    # property is equivalence at end time of each system
    prop = timed_sys_equiv[-1]
    for i in range(1, len(timed_actions[0])):
        print("======= Proving that an action can be delayed for instruction cardinality = {} ======".format(i+1))
        antecedent = sn[i]
        if i < len(timed_actions[0]) - 1:
            # it's exactly i+1 actions enabled, e.g. don't let it be more
            antecedent = And(antecedent, Not(sn[i+1]))

        res = True

        while res:
            assumptions = [antecedent, Not(prop)]
            res = bmc.solver.solver.solve(assumptions)

            if res:
                model = bmc.solver.solver.get_model()
                failed_equivalences = []
                for c in conjunctive_partition(timed_sys_equiv[-1]):
                    v = c.serialize(100)
                    if not bmc.solver.solver.get_value(c).constant_value():
                        failed_equivalences.append(v)
                witness_antecedent = []
                witness_neg_consequent = []
                complex_instruction = []
                for ta in timed_actions[0]:
                    vta = bmc.solver.solver.get_value(ta).constant_value()
                    if vta:
                        complex_instruction.append(ta)
                        witness_antecedent.append(ta)
                    else:
                        complex_instruction.append(Not(ta))

                if not monotonic:
                    # create shallow copy
                    witness_antecedent = list(complex_instruction)
                    witness_antecedent.append(Not(prop))

                # now add predicates
                for p in predicates:
                    vp = bmc.solver.solver.get_value(p).constant_value()
                    if vp:
                        witness_antecedent.append(p)
                    else:
                        witness_antecedent.append(Not(p))

                # only considering time 0 and only allow delayed action at time 1
                # to be more general, could let the witness constraint range over time 0 and time 1
                for cta in copy_timed_actions[0]:
                    vcta = bmc.solver.solver.get_value(cta).constant_value()
                    if vcta:
                        witness_neg_consequent.append(cta)
                    else:
                        witness_neg_consequent.append(Not(cta))
                vdelay = bmc.solver.solver.get_value(delay_sel)
                witness_constraint = Implies(And(witness_antecedent), Not(EqualsOrIff(delay_sel, vdelay)))

                # # debugging
                # debug_delay_val = vdelay.constant_value()
                # debug_action_vars = [bmc.solver.solver.get_value(a).constant_value() for a in timed_actions[0]]
                # debug_copy_action_vars = [bmc.solver.solver.get_value(a).constant_value() for a in copy_timed_actions[0]]
                # debug_action_delayed = bmc.solver.solver.get_value(copy_timed_actions[1][debug_delay_val]).constant_value()

                # print('debug_delay_val', debug_delay_val)
                # print('debug_action_vars', debug_action_vars)
                # print('debug_copy_action_vars', debug_copy_action_vars)
                # print('debug_action_delayed', debug_action_delayed)
                # if debug_action_vars == [True, True, True, True, False] and \
                #    debug_copy_action_vars == [False, True, True, True, False] and \
                #    debug_delay_val == 0 and \
                #    debug_action_delayed:
                #     model = bmc.solver.solver.get_model()
                #     print(model)
                #     raise RuntimeError("Hit case")
                # # end debugging

                print()
                print("Learned witness constraint:")
                assume(bmc, witness_constraint, serialize=100)
                print()

                # check that we haven't over-constrained with the learned witness
                if not bmc.solver.solver.solve([antecedent, And(complex_instruction)]):
                    print("Previous model")
                    print(model)

                    print("Failed with complex instruction:", complex_instruction)
                    print("Failed equivalences:\n")
                    print("\n\t".join(failed_equivalences))
                    raise RuntimeError("Bummer: Over-constrained by witness -- giving up")

            else:
                continue
    return True

strategies = {
    'simple': simple_delay_strategy,
    'simple-ceg': simple_ceg_strategy,
    'ceg': ceg_strategy
}

def reduced_instruction_set(hts, config, generic_interface, strategy='simple', predicates:Optional[List[FNode]]=None):
    unrolled_sys = ris_proof_setup(hts, config, generic_interface)

    bmc = unrolled_sys.bmc
    timed_actions = unrolled_sys.timed_actions
    timed_sys_equiv = unrolled_sys.timed_sys_equiv

    # cover -- not equal
    res = bmc.solver.solver.solve([Not(timed_sys_equiv[-1])])
    assert res
    # if res:
    #     model = bmc.solver.solver.get_model()
    #     print('+++++++++++++++++++++++++++ Model ++++++++++++++++++++++++++++')
    #     print(model)

    delay_sel, delay, sn = setup_delay_logic(unrolled_sys)

    # another cover after the delay logic is added
    # can't expect there to be a trace resulting in different states after delay logic added
    res = bmc.solver.solver.solve()
    assert res

    res = strategies[strategy](unrolled_sys, delay, sn, predicates=predicates, delay_sel=delay_sel)

    if res:
        print("Property holds")
        print("IMPORTANT NOTE: This procedure for finding the reduced instruction set relies on proving that actions don't disable each other -- use IC3 for this.")

    else:
        raise RuntimeError("Bummer: {} delay failed -- try a more advanced approach".format(strategy))

    return res

def create_action_constraints(hts, config, generic_interface)->FNode:
    '''
    Creates a disjunctive constraint for reduced instruction sets.
    Assumes that reduced_instruction_set was called and returned True, i.e. all actions can be separated
    '''

    actions = generic_interface.actions
    disjuncts = []
    for i in range(len(actions)):
        conjuncts = []
        for j, a in enumerate(actions):
            if i == j:
                conjuncts.append(a)
            else:
                conjuncts.append(Not(a))
        disjuncts.append(And(conjuncts))

    assert len(disjuncts) > 0, "Expecting non-empty disjunction"

    if not safe_to_remove_empty_instruction(hts, config, generic_interface):
        print("Cannot remove empty instruction")
        disjuncts.append(And([Not(a) for a in actions]))
    else:
        print("Can safely remove empty instruction")

    return Or(disjuncts)

def safe_to_remove_empty_instruction(hts:HTS, config:NamedTuple, generic_interface:interface)->bool:
    '''
    Returns true if we can remove the empty instruction (e.g. no actions, a stutter step)
    '''
    B = 2

    bmc = BMCSolver(hts, config)
    bmc._init_at_time(hts.vars, 2)

    invar = hts.single_invar()
    trans = hts.single_trans()
    invar0 = bmc.at_time(invar, 0)

    assume(bmc, invar0, "Assuming invariant at 0")

    unrolled = bmc.unroll(trans, invar, B)
    assume(bmc, unrolled, "Assuming unrolled system")

    timed_actions = defaultdict(list)
    timed_ens     = defaultdict(list)
    timed_data_inputs = defaultdict(list)
    for t in range(B):
        for a in generic_interface.actions:
            timed_actions[t].append(bmc.at_time(a, t))
        for e in generic_interface.ens:
            timed_ens[t].append(bmc.at_time(e, t))
        for di in generic_interface.data_inputs:
            timed_data_inputs[t].append(bmc.at_time(di, t))
        assert len(timed_actions[t]) == len(timed_ens[t])

    assert hts.state_vars, "Expecting at least one state variable"
    state_changed = Not(And([EqualsOrIff(bmc.at_time(sv, 0), bmc.at_time(sv, 1)) for sv in hts.state_vars]))

    return not bmc.solver.solver.solve([Not(Or(timed_actions[0])), state_changed])

def read_verilog(filepath:Path, topmod:str, config:btor_config)->Tuple[HTS, FNode, FNode]:
    parser = VerilogYosysBtorParser()
    return parser.parse_file(filepath, config, flags=[topmod])

def read_btor(filepath:Path, topmod:str, config:btor_config)->Tuple[HTS, FNode, FNode]:
    parser = BTOR2Parser()
    return parser.parse_file(filepath, config, flags=[topmod])
