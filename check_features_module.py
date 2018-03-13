import logging as log
import z3
import uuid
import json

def run_feature_analysis_with_optimization(
        features,
        contexts,
        attributes,
        constraints,
        optional_features,
        non_incremental_solver,
        out_stream,
        time_context=""):
    """
    Performs the feature analysis task.
    Assumes the interface with non boolean features
    """

    data = {"dead_features": {}, "false_optionals": {}}
    #solver = z3.Optimize()
    solver = z3.Solver()
    #solver = z3.Then('simplify', 'nla2bv', 'smt').solver()
    if non_incremental_solver:
        solver.set("combined_solver.solver2_timeout",1)

    log.info("Add variables")
    for i in features:
        solver.add(0 <= z3.Int(i), z3.Int(i) <= 1)
    for i in attributes.keys():
        solver.add(attributes[i]["min"] <= z3.Int(i), z3.Int(i) <= attributes[i]["max"])
    for i in contexts.keys():
        solver.add(contexts[i]["min"] <= z3.Int(i), z3.Int(i) <= contexts[i]["max"])

    log.info("Add constraints")
    for i in constraints:
        solver.add(i)

    # if time variable is not defined, create a fictional one
    if time_context == "":
        time_context = "_" + uuid.uuid4().hex
        for i in optional_features:
            optional_features[i].append((0,0))

    if not non_incremental_solver:
        log.debug("Preliminary check")
        solver.check()

    # list of the features to check
    to_check_dead = {}
    to_check_false = {}
    for i in optional_features:
        for k in optional_features[i]:
            for j in range(k[0],k[1]+1):
                if j in to_check_dead:
                    to_check_dead[j].add(i)
                    to_check_false[j].add(i)
                else:
                    to_check_dead[j] = set([i])
                    to_check_false[j] = set([i])

    log.debug(unicode(solver))

    log.info("Computing dead or false optional features considering {} optional features".format(len(optional_features)))
    log.debug("Features to check: {}".format(to_check_dead))

    for i in to_check_dead:
        log.debug("Processing time instant {}, features to check {}".format(i,len(to_check_dead[i])))
        solver.push()
        solver.add(z3.Int(time_context).__eq__(z3.IntVal(i)))

        if not non_incremental_solver:
            log.debug("Preliminary check")
            solver.check()

        solver.push()

        log.debug("Checking for dead features")
        limit = 64
        all_in_once = max(len(to_check_dead[i])/2,1)
        all_in_once = min(limit,all_in_once)

        while to_check_dead[i]:
            log.debug("{} ({}) dead (false optional) features to check".format(
                len(to_check_dead[i]), len(to_check_false[i])))

            if all_in_once == 1:
                solver.set('smt.timeout',4294967295)
                solver.add(z3.Or([z3.Int(j).__eq__(z3.IntVal(1)) for j in to_check_dead[i]]))
            else:
                solver.push()
                solver.set('smt.timeout', 30000)
                log.debug("Attempt to prune {} features at once".format(all_in_once))
                solver.add(z3.PbGe([(z3.Int(j).__eq__(z3.IntVal(1)), 1) for j in to_check_dead[i]], all_in_once))

            result = solver.check()
            log.debug("Solver result {}".format(result))
            if result == z3.unsat:
                if all_in_once == 1:
                    to_check_false[i].difference_update(to_check_dead[i])
                    for j in to_check_dead[i]:
                        if j in data["dead_features"]:
                            data["dead_features"][j].append(i)
                        else:
                            data["dead_features"][j] = [i]
                    break
                else:
                    solver.pop()
                    all_in_once = max(all_in_once/2, 1)
            elif result == z3.sat:
                model = solver.model()
                to_remove_dead = []
                to_remove_false = []
                for j in to_check_dead[i]:
                    if model[z3.Int(j)] == z3.IntVal(1):
                        to_remove_dead.append(j)
                for j in to_check_false[i]:
                    if model[z3.Int(j)] == z3.IntVal(0):
                        to_remove_false.append(j)
                log.debug("Removed {} ({}) dead (false optional) checks".format(
                    len(to_remove_dead), len(to_remove_false)))
                to_check_dead[i].difference_update(to_remove_dead)
                to_check_false[i].difference_update(to_remove_false)

                if all_in_once != 1:
                    solver.pop()
                all_in_once = max(min(all_in_once,len(to_check_dead[i]) / 2), 1)
                all_in_once = min(limit, all_in_once)
            else:
                log.debug("Execution not terminated without the timeout. Moving on")
                solver.pop()
                all_in_once = max(all_in_once / 2, 1)

        solver.pop()
        solver.push()

        log.debug("Checking for false optional features")
        while to_check_false[i]:
            log.debug("{} false optional features to check".format(len(to_check_false[i])))
            solver.add(z3.Or([z3.Int(j).__eq__(z3.IntVal(0)) for j in to_check_false[i]]))
            result = solver.check()
            if result == z3.unsat:
                for j in to_check_false[i]:
                    if j in data["false_optionals"]:
                        data["false_optionals"][j].append(i)
                    else:
                        data["false_optionals"][j] = [i]
                break
            elif result == z3.sat:
                model = solver.model()
                for j in to_check_false[i].copy():
                    if model[z3.Int(j)] == z3.IntVal(0):
                        to_check_false[i].discard(j)
        solver.pop()
        solver.pop()

    log.info("Printing output")
    json.dump(data, out_stream)
    out_stream.write("\n")



def my_test(
        features,
        contexts,
        attributes,
        constraints,
        optional_features,
        non_incremental_solver,
        out_stream,
        time_context=""):
    """
    Performs the feature analysis task.
    Assumes the interface with non boolean features
    """

    data = {"dead_features": {}, "false_optionals": {}}
    solver = z3.Solver()
    # if non_incremental_solver:
    #     solver.set("combined_solver.solver2_timeout",1)

    log.info("Building the FM formula")
    formulas = []

    for i in attributes.keys():
        formulas.append(attributes[i]["min"] <= z3.Int(i))
        formulas.append(z3.Int(i) <= attributes[i]["max"])

    for i in constraints:
        formulas.append(i)


    # if time variable is not defined, create a fictional one
    if time_context == "":
        time_context = "_" + uuid.uuid4().hex
        for i in optional_features:
            optional_features[i].append((0,0))

    fresh_var = "_" + uuid.uuid4().hex

    # if not non_incremental_solver:
    #     log.debug("Preliminary check")
    #     solver.check()

    # list of the features to check
    to_check_dead = {}
    to_check_false = {}
    for i in optional_features:
        for k in optional_features[i]:
            for j in range(k[0],k[1]+1):
                if j in to_check_dead:
                    to_check_dead[j].append(i)
                    to_check_false[j].append(i)
                else:
                    to_check_dead[j] = [i]
                    to_check_false[j] = [i]

    log.debug(unicode(solver))

    log.info("Computing dead or false optional features considering {} optional features".format(len(optional_features)))
    log.debug("Features to check: {}".format(to_check_dead))

    for i in to_check_dead:

        log.debug("Processing time instant {}, features to check {}".format(i,len(to_check_dead[i])))
        solver.push()
        solver.add(z3.Int(time_context).__eq__(z3.IntVal(i)))

        # if not non_incremental_solver:
        #     log.debug("Preliminary check")
        #     solver.check()

        solver.add(0 <= z3.Int(fresh_var))
        solver.add(z3.Int(fresh_var) < z3.IntVal(len(to_check_dead[i])))



        solver.add()

        # exist d in DeadF . for all features/attributes f_d = 0 \/ not FD
        solver.add(z3.ForAll([z3.Int(j) for j in features] + [z3.Int(j) for j in attributes.keys()],
            z3.Implies(
                z3.And([z3.Implies(z3.Int(fresh_var).__eq__(z3.IntVal(j)),
                               z3.Int(to_check_dead[i][j]).__eq__(z3.IntVal(1)))
                    for j in range(len(to_check_dead[i]))]),
                z3.Not(z3.And(formulas)))))

        log.debug(unicode(solver))

        log.info("Computing")
        result = solver.check()
        log.info("Printing output")

        if result == z3.sat:
            model = solver.model()
            # out = {"result": "not_valid", "contexts": []}
            # for i in contexts.keys():
            #     out["contexts"].append({"id": i, "value": unicode(model[z3.Int(i)])})
            # json.dump(out, out_stream)
            value = model[z3.Int(fresh_var)].as_long()
            log.critical("Dead feature for time {}: {}".format(i, to_check_dead[i][value]))
            out_stream.write("\n")
        else:
            out_stream.write('Unsat\n')
        solver.pop()
