import logging as log
import z3
import json
import itertools


def run_validate(
        features,
        initial_features,
        contexts,
        attributes,
        constraints,
        preferences,
        context_constraints,
        features_as_boolean,
        out_stream):
    """
    Perform the validation task using the formula with quantifiers
    """
    solver = z3.Solver()
    solver.set("smt.relevancy",0)

    log.info("Add context variables")
    for i in list(contexts.keys()):
        solver.add(contexts[i]["min"] <= z3.Int(i), z3.Int(i) <= contexts[i]["max"])

    log.info("Add contexts constraints")
    for i in context_constraints:
        solver.add(i)

    log.info("Building the FM formula")
    formulas = []
    if not features_as_boolean:
        for i in features:
            formulas.append(0 <= z3.Int(i))
            formulas.append(z3.Int(i) <= 1)

    for i in list(attributes.keys()):
        formulas.append(attributes[i]["min"] <= z3.Int(i))
        formulas.append(z3.Int(i) <= attributes[i]["max"])

    for i in constraints:
        formulas += i

    log.info("Add forall not FM formula")
    if features_as_boolean:
        solver.add(z3.ForAll(
            [z3.Bool(i) for i in features] + [z3.Int(i) for i in list(attributes.keys())],
            z3.Not(z3.And(formulas))
        ))
    else:
        solver.add(z3.ForAll(
            [z3.Int(i) for i in features] + [z3.Int(i) for i in list(attributes.keys())],
            z3.Not(z3.And(formulas))
        ))
    log.debug(solver)

    log.info("Computing")
    result = solver.check()
    log.info("Printing output")

    if result == z3.sat:
        model = solver.model()
        out = {"result": "not_valid", "contexts": []}
        for i in list(contexts.keys()):
            out["contexts"].append({"id": i, "value": str(model[z3.Int(i)])})
        json.dump(out, out_stream)
        out_stream.write("\n")
    else:
        out_stream.write('{"result":"valid"}\n')


def run_validate_grid_search(
        features,
        initial_features,
        contexts,
        attributes,
        constraints,
        preferences,
        context_constraints,
        features_as_boolean,
        non_incremental_solver,
        out_stream):
    """
    Perform the validation task
    Grid search. Every context is tried
    """
    solver = z3.Solver()
    if non_incremental_solver:
        log.info("Non incremental solver modality activated")
        solver.set("combined_solver.solver2_timeout",1)

    # compute grid
    contexts_names = list(contexts.keys())
    context_ranges = [list(range(contexts[i]["min"],contexts[i]["max"]+1)) for i in contexts_names]
    products = list(itertools.product(*context_ranges))
    if not contexts_names: # no context is defined
        products = [[]]
    log.info("{} Context combination to try".format(len(products)))

    log.info("Add variables")
    if not features_as_boolean:
        for i in features:
            solver.add(0 <= z3.Int(i), z3.Int(i) <= 1)
    for i in list(attributes.keys()):
        solver.add(attributes[i]["min"] <= z3.Int(i), z3.Int(i) <= attributes[i]["max"])
    for i in list(contexts.keys()):
        solver.add(contexts[i]["min"] <= z3.Int(i), z3.Int(i) <= contexts[i]["max"])

    log.info("Add constraints")
    for i in constraints:
        solver.add(i)

    if not non_incremental_solver:
        log.info("Precheck")
        solver.check()

    for i in products:
        log.info("Exploring product {}".format(i))
        solver.push()
        for j in range(len(i)):
            solver.add(i[j] == z3.Int(contexts_names[j]))
        result = solver.check()
        if result == z3.unsat:
            if context_constraints:
                log.debug("Checking the context constraints are not violated")
                # check that context_constraints are not violated
                solver1 = z3.Solver()
                for j in range(len(i)):
                    solver1.add(products[j] == z3.Int(contexts_names[j]))
                solver1.add(context_constraints)
                if solver1.check() != z3.sat:
                    continue
            out = {"result": "not_valid", "contexts": []}
            for j in range(len(i)):
                out["contexts"].append({"id": contexts_names[j], "value": str(i[j])})
            json.dump(out, out_stream)
            out_stream.write("\n")
            return
        solver.pop()
    out_stream.write('{"result":"valid"}\n')