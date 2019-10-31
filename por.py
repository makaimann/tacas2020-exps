from collections import defaultdict, namedtuple
from cosa.analyzers.mcsolver import BMCSolver
from cosa.utils.formula_mngm import substitute, get_free_variables
from cosa.representation import HTS, TS
from typing import List, NamedTuple, Tuple, Optional
from pysmt.fnode import FNode
from pysmt.shortcuts import And, BOOL, BV, BVULE, BVType, EqualsOrIff, Implies, Not, Or, simplify, Solver, Symbol, TRUE
from pysmt.rewritings import conjunctive_partition

from por_utils import assume, copy_sys, interface

def find_gir(hts:HTS, config:NamedTuple, generic_interface:interface, guards:Optional[List[FNode]]=None)->List[Tuple[FNode, FNode]]:
    '''
    Automatically find guarded independence relationships, aka partial order reductions
    '''

    B = 3

    copy_hts, copy_interface, sys_equiv_output, _ = copy_sys(hts, generic_interface)
    hts_comb = HTS()
    hts_comb.combine(hts)
    hts_comb.combine(copy_hts)

    bmc = BMCSolver(hts_comb, config)
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

    timed_sys_equiv = list()
    for t in range(B):
        timed_sys_equiv.append(bmc.at_time(sys_equiv_output, t))

    assume(bmc, timed_sys_equiv[0], "Assuming they start in the same state.")

    print("Add assumptions about copy data")
    for i in range(len(generic_interface.data_inputs)):
        assume(bmc, EqualsOrIff(copy_timed_data_inputs[0][i], timed_data_inputs[1][i]))
        assume(bmc, EqualsOrIff(copy_timed_data_inputs[1][i], timed_data_inputs[0][i]))

    girs = []
    for i in range(len(generic_interface.actions)-1):
        for j in range(i+1, len(generic_interface.actions)):
            print("Checking {} and {} for an independence relationship".format(generic_interface.actions[i], generic_interface.actions[j]))
            a0i, a1j = timed_actions[0][i], timed_actions[1][j]
            ca0j, ca1i = copy_timed_actions[0][j], copy_timed_actions[1][i]
            assumptions = [a0i, a1j, ca0j, ca1i, Not(timed_sys_equiv[2])]
            if not bmc.solver.solver.solve(assumptions):
                print("Found an independence relationship.")
                girs.append((generic_interface.actions[i], generic_interface.actions[j], TRUE()))
            else:
                model = bmc.solver.solver.get_model()
                # print(model)
                # raise RuntimeError() #temporary for debugging
                failed_equivalences = []
                for c in conjunctive_partition(timed_sys_equiv[2]):
                    v = c.serialize(100)
                    if not bmc.solver.solver.get_value(c).constant_value():
                        failed_equivalences.append(v)

                print("An independence relationship check failed.")
                if guards is not None:
                    print("Trying guards.")
                    # add an empty slot for guard
                    assumptions.append(None)
                    for g in guards:
                        # use guard at time 0
                        assumptions[-1] = bmc.at_time(g, 0)
                        if not bmc.solver.solver.solve(assumptions):
                            print("Found a guarded independence relationship.")
                            girs.append((generic_interface.actions[i], generic_interface.actions[j], g))
                        else:
                            print("Failed equivalences:\n")
                            print("\n\t".join(failed_equivalences))
                    # # debugging
                    # model = bmc.solver.solver.get_model()
                    # print(model)
                    # # end debugging
    return girs
