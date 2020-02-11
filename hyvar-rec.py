__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2016, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.2"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

import sys
import os
import logging as log
import json
import re
# use multiprocessing because antlr is not thread safe
import multiprocessing
import click
import z3
import datetime

import SpecificationGrammar.SpecTranslator as SpecTranslator

DEVNULL = open(os.devnull, 'wb')

def usage():
    """Print usage"""
    print(__doc__)


def read_json(json_file):
    json_data = open(json_file)
    data = json.load(json_data)
    json_data.close()
    return data


# function to encode SMT expression into SMTLIB
def toSMT2(f, status="unknown", name="benchmark", logic=""):
  v = (z3.Ast * 0)()
  return z3.Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast()).replace(
      "\n"," ").replace("(check-sat)","").replace("; benchmark (set-info :status unknown)","").strip()

def get_true_boolean_features_from_model(model):
    ls = []
    for decl in model.decls():
        if z3.is_true(model[decl]):
            if not "!" in decl.__repr__():
                ls.append(decl.__repr__())
    return ls

def run_reconfigure(
        features,
        initial_features,
        contexts,
        attributes,
        constraints,
        preferences,
        features_as_boolean,
        timeout,
        no_default_preferences,
        out_stream):
    """Perform the reconfiguration task
    """
    solver = z3.Optimize()

    log.info("Add variables")
    if not features_as_boolean:
        for i in features:
            solver.add(0 <= z3.Int(i), z3.Int(i) <= 1)
    for i in list(attributes.keys()):
        solver.add(attributes[i]["min"] <= z3.Int(i), z3.Int(i) <= attributes[i]["max"])
    for i in list(contexts.keys()):
        solver.add(contexts[i]["min"] <= z3.Int(i), z3.Int(i) <= contexts[i]["max"])

    log.info("Enforce context to be equal to intial values")
    for i in list(contexts.keys()):
        solver.add(contexts[i]["initial"] == z3.Int(i))

    log.info("Add constraints")
    for i in constraints:
        solver.add(i)

    log.info("Add preferences")
    for i in preferences:
        solver.maximize(i)

    if no_default_preferences:
        log.info("Default preferences will be ignored.")
    else:
        log.info("Add preference: minimize the number of initial features removed")
        if initial_features:
            if features_as_boolean:
                solver.maximize(z3.Sum([z3.If(z3.Bool(i),1,0) for i in initial_features]))
            else:
                solver.maximize(z3.Sum([z3.Int(i) for i in initial_features]))

        log.info("Add preference: minimize the number of attributes changed")
        initial_attributes = [k for k in list(attributes.keys()) if "initial" in attributes[k]]
        if initial_attributes:
            solver.maximize(
                z3.Sum([z3.If(z3.Int(i) == z3.IntVal(attributes[i]["initial"]), 1, 0) for i in initial_attributes]))

        log.info("Add preference: minimize the number of non initial features added")
        if features.difference(initial_features):
            if features_as_boolean:
                solver.minimize(z3.Sum([z3.If(z3.Bool(i),1,0) for i in features.difference(initial_features)]))
            else:
                solver.minimize(z3.Sum([z3.Int(i) for i in features.difference(initial_features)]))

        log.info("Add preference: minimize the values of the attributes")
        for i in list(attributes.keys()):
            solver.minimize(z3.Int(i))

    #log.debug(unicode(solver))

    if timeout > 0:
        solver.set("timeout", timeout)

    log.info("Computing reconfiguration")
    result = solver.check()

    log.info("Printing output")
    if result == z3.sat:
        model = solver.model()
        out = {"result": "sat", "features": [], "attributes": []}
        if features_as_boolean:
            out["features"].extend(get_true_boolean_features_from_model(model))
        else:
            for i in features:
                if model[z3.Int(i)] == z3.IntVal(1):
                    out["features"].append(i)
        for i in list(attributes.keys()):
            if attributes[i]["feature"] in out["features"]:
                out["attributes"].append({"id": i, "value": str(model[z3.Int(i)])})
        json.dump(out, out_stream)
        out_stream.write("\n")
    else:
        out_stream.write('{"result": "unsat"}\n')


def run_explain(
        features,
        contexts,
        attributes,
        constraints,
        data,
        features_as_boolean,
        constraints_minimization,
        out_stream):
    """Get the explanation of the unsat of the FM model
    """
    solver = z3.Solver()
    solver.set(unsat_core=True)

    # minimize the explanations
    if constraints_minimization:
        solver.set("smt.core.minimize",True)

    log.info("Add variables")
    if not features_as_boolean:
        for i in features:
            solver.add(0 <= z3.Int(i), z3.Int(i) <= 1)
    for i in list(attributes.keys()):
        solver.add(attributes[i]["min"] <= z3.Int(i), z3.Int(i) <= attributes[i]["max"])
    for i in list(contexts.keys()):
        solver.add(contexts[i]["min"] <= z3.Int(i), z3.Int(i) <= contexts[i]["max"])

    log.info("Enforce context to be equal to initial values")
    for i in list(contexts.keys()):
        solver.add(contexts[i]["initial"] == z3.Int(i))

    log.info("Add constraints")
    counter = 0
    for i in constraints:
        solver.assert_and_track(i, 'aux' + str(counter))
        counter += 1

    log.info("Computing reconfiguration")
    result = solver.check()

    log.info("Printing output")
    if result == z3.sat:
        model = solver.model()
        out = {"result": "sat", "features": [], "attributes": []}
        if features_as_boolean:
            out["features"].extend(get_true_boolean_features_from_model(model))
        else:
            for i in features:
                if model[z3.Int(i)] == z3.IntVal(1):
                    out["features"].append(i)
        for i in list(attributes.keys()):
            if attributes[i]["feature"] in out["features"]:
                out["attributes"].append({"id": i, "value": str(model[z3.Int(i)])})
        json.dump(out, out_stream)
        out_stream.write("\n")
    else:
        core = solver.unsat_core()
        log.debug("Core: " + str(core))
        out = {"result": "unsat", "constraints": []}
        for i in range(len(constraints)):
            if z3.Bool('aux' + str(i)) in core:
                out["constraints"].append(data["constraints"][i])
        json.dump(out, out_stream)
        out_stream.write("\n")


def run_check_interface(features,
                        contexts,
                        attributes,
                        constraints,
                        contexts_constraints,
                        interface,
                        features_as_boolean,
                        out_stream):
    """Check if the interface given is a proper interface
    """
    # todo possibility of using interface where features are given as boolean and not int
    # handle FM contexts_constraints
    i_features = set()
    i_contexts = {}
    i_attributes = {}
    i_constraints = []
    i_contexts_constraints = []

    log.info("Processing interface attributes")
    for i in interface["attributes"]:
        id = re.match("attribute\[(.*)\]", i["id"]).group(1)
        i_attributes[id] = {}
        i_attributes[id]["min"] = i["min"]
        i_attributes[id]["max"] = i["max"]
        i_attributes[id]["feature"] = re.match("feature\[(.*)\]", i["featureId"]).group(1)
        if (id not in attributes) or \
            (attributes[id]["min"] < i_attributes[id]["min"]) or \
            (attributes[id]["max"] > i_attributes[id]["max"]) :
            json.dump({"result": "not_valid: attribute " + id + "does not match"}, out_stream)
            out_stream.write("\n")
            return None
    log.debug(str(attributes))

    log.info("Processing contexts")
    for i in interface["contexts"]:
        id = re.match("context\[(.*)\]", i["id"]).group(1)
        i_contexts[id] = {}
        i_contexts[id]["min"] = i["min"]
        i_contexts[id]["max"] = i["max"]
        if (id not in contexts) or \
                (contexts[id]["min"] == i_contexts[id]["min"]) or \
                (contexts[id]["max"] == i_contexts[id]["max"]):
            json.dump({"result": "not_valid: context " + id + "does not match"}, out_stream)
            out_stream.write("\n")
            return None
    log.debug(str(contexts))

    log.info("Processing Constraints")
    for i in interface["constraints"]:
        try:
            d = SpecTranslator.translate_constraint(i, interface, features_as_boolean)
            log.debug("Find constraint " + str(d))
            i_constraints.append(d["formula"])
            i_features.update(d["features"])
        except Exception as e:
            log.critical("Parsing failed while processing " + i + ": " + str(e))
            log.critical("Exiting")
            sys.exit(1)

    log.info("Processing Context Constraints")
    if "context_constraints" in interface:
        for i in interface["context_constraints"]:
            try:
                d = SpecTranslator.translate_constraint(i, interface, features_as_boolean)
                log.debug("Find context constraint " + str(d))
                i_contexts_constraints.append(d["formula"])
            except Exception as e:
                log.critical("Parsing failed while processing " + i + ": " + str(e))
                log.critical("Exiting")
                sys.exit(1)

    log.info("Checking Context Constraints Extensibility")
    solver = z3.Solver()
    for i in list(contexts.keys()):
        solver.add(contexts[i]["min"] <= z3.Int(i))
        solver.add(z3.Int(i) <= contexts[i]["max"])
    solver.add(z3.And(i_contexts_constraints))
    solver.add(z3.Not(z3.And(contexts_constraints)))
    result = solver.check()

    if result == z3.sat:
        model = solver.model()
        out = {"result": "not_valid: context extensibility problem", "contexts": []}
        for i in list(contexts.keys()):
            out["contexts"].append({"id": i, "value": str(model[z3.Int(i)])})
        json.dump(out, out_stream)
        out_stream.write("\n")

    solver = z3.Solver()

    log.info("Add interface variables")
    if not features_as_boolean:
        for i in i_features:
            solver.add(0 <= z3.Int(i), z3.Int(i) <= 1)
    for i in list(i_attributes.keys()):
        solver.add(i_attributes[i]["min"] <= z3.Int(i), z3.Int(i) <= i_attributes[i]["max"])
    for i in list(i_contexts.keys()):
        solver.add(i_contexts[i]["min"] <= z3.Int(i), z3.Int(i) <= i_contexts[i]["max"])

    log.info("Add interface contexts constraints")
    solver.add(z3.And(i_contexts_constraints))
    solver.add(z3.And(contexts_constraints))

    log.info("Add interface constraints")
    for i in i_constraints:
        solver.add(i)

    log.info("Add FM context variables")
    for i in list(contexts.keys()):
        if i not in i_contexts:
            solver.add(contexts[i]["min"] <= z3.Int(i))
            solver.add(z3.Int(i) <= contexts[i]["max"])

    log.info("Building the FM formula")
    formulas = []
    if not features_as_boolean:
        for i in features:
            if i not in i_features:
                formulas.append(0 <= z3.Int(i))
                formulas.append(z3.Int(i) <= 1)
    for i in list(attributes.keys()):
        if i not in i_attributes:
            formulas.append(attributes[i]["min"] <= z3.Int(i))
            formulas.append(z3.Int(i) <= attributes[i]["max"])
    for i in constraints:
        formulas.append(i)

    log.info("Add forall fatures and attributes not formula")
    if features_as_boolean:
        #todo fix print when features are given as booleans
        solver.add(z3.ForAll(
            [z3.Bool(i) for i in features if i not in i_features] +
            [z3.Int(i) for i in list(attributes.keys()) if i not in list(i_attributes.keys())],
            z3.Not(z3.And(formulas))
        ))
    else:
        solver.add(z3.ForAll(
            [z3.Int(i) for i in features if i not in i_features] +
            [z3.Int(i) for i in list(attributes.keys()) if i not in list(i_attributes.keys())],
            z3.Not(z3.And(formulas))
        ))

    log.debug(solver)

    log.info("Computing")
    result = solver.check()
    log.info("Printing output")

    if result == z3.sat:
        model = solver.model()
        out = {"result": "not_valid", "contexts": [], "attributes": [], "features" : []}
        for i in list(contexts.keys()):
            out["contexts"].append({"id": i, "value": str(model[z3.Int(i)])})
        if features_as_boolean:
            for i in i_features:
                out["features"].append({"id": i, "value": str(model[z3.Bool(i)])})
        else:
            for i in i_features:
                out["features"].append({"id": i, "value": str(model[z3.Int(i)])})
        for i in list(i_attributes.keys()):
            out["attributes"].append({"id": i, "value": str(model[z3.Int(i)])})
        json.dump(out, out_stream)
        out_stream.write("\n")
    else:
        out_stream.write('{"result":"valid"}\n')


def translate_constraints(triple):
    c,data,features_as_boolean = triple
    try:
        d = SpecTranslator.translate_constraint(c, data, features_as_boolean)
    except Exception as e:
        log.critical("Parsing failed while processing " + c + ": " + str(e))
        log.critical("Exiting")
        sys.exit(1)
    return toSMT2(d["formula"]),d["features"]




@click.command()
@click.argument('input_file',
    type=click.Path(exists=True, file_okay=True, dir_okay=False, writable=False, readable=True, resolve_path=True))
@click.option('--num-of-process', '-p', type=click.INT, default=1,
              help='Number of process to use for translating the dependencies.')
@click.option('--output-file', '-o',
              type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True),
              help='Output file - Otherwise the output is printed on stdout.')
@click.option('--keep', '-k', is_flag=True,
              help="Do not convert dependencies into SMT formulas.")
@click.option('--verbose', '-v', count=True,
              help="Print debug messages.")
@click.option('--validate', is_flag=True,
              help="Activate the validation mode to check if for all context the FM is not void.")
@click.option('--validate-modality',
              help="Modality for conducting the validation",
              default="forall",
              type=click.Choice(["grid", "forall"]),
              show_default=True)
@click.option('--explain', is_flag=True,
              help="Tries to explain why a FM is void.")
@click.option('--check-interface',
              default="",
              help="Checks if the interface given as additional file is a proper interface.")
@click.option('--features-as-boolean', is_flag=True,
              help="Require features in constraints defined as booleans.")
@click.option('--check-features', is_flag=True,
              help="Starts the check to list all the mandatory and dead features.")
@click.option('--check-features-modality',
              help="Modality for conducting the check feature search.",
              default="forall",
              type=click.Choice(["grid", "forall", "pruning"]),
              show_default=True)
@click.option('--stop-at-first-anomaly', is_flag=True,
              help="Stop the check feature task as soon as one feature anomaly is detected.")
@click.option('--timeout', type=click.INT, default=0,
              help="Timeout in milliseconds for the solver (0 = no-timeout). Valid only when used in reconfiguration mode.")
@click.option('--constraints-minimization', is_flag=True,
              help="Try to produce a minimal explanation. Option valid only in explanation mode.")
@click.option('--no-default-preferences', is_flag=True,
              help="Do not consider default preferences to minimize the difference w.r.t. the initial configuration. Option significant only in reconfiguration mode.")
@click.option('--non-incremental-solver', is_flag=True,
              help="Set the timeout for the incremental solver of Z3 to 1.")
def main(input_file,
         num_of_process,
         output_file,
         keep,
         verbose,
         validate,
         validate_modality,
         explain,
         check_interface,
         features_as_boolean,
         check_features,
         check_features_modality,
         timeout,
         constraints_minimization,
         non_incremental_solver,
         no_default_preferences,
         stop_at_first_anomaly):
    """
    INPUT_FILE Json input file
    """

    start_time = datetime.datetime.now()
    modality = "reconfigure" # default modality is to proceed with the reconfiguration
    interface_file = ""

    # only one modality can be active
    if sum([validate,explain,check_features,(len(check_interface) > 0)]) > 1:
        log.critical("Only one flag among validate, explain, check-interface, and check-feature can be selected.")
        sys.exit(1)

    if check_interface and features_as_boolean:
        log.critical("Features check-interface and features-as-boolean are incompatible, only one can be selected.")
        sys.exit(-1)

    if validate:
        modality = "validate"
    if explain:
        modality = "explain"
    if check_interface:
        modality = "check-interface"
        interface_file = check_interface
    if check_features:
        modality = "check-features"

    log_level = log.ERROR
    if verbose == 1:
        log_level = log.WARNING
    elif verbose == 2:
        log_level = log.INFO
    elif verbose >= 3:
        log_level = log.DEBUG
    log.basicConfig(format="[%(asctime)s][%(levelname)s][%(name)s]%(message)s",level=log_level)
    log.info("Verbose Level: " + str(verbose))

    if verbose:
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
        log.info("Verbose output.")

    if keep:
        global KEEP
        KEEP = True

    out_stream = sys.stdout
    if output_file:
        out_stream = open(output_file, "w")

    features = set()
    initial_features = set()
    contexts = {}
    attributes = {}
    constraints = []
    preferences = []
    contexts_constraints = []
    log.info("Reading input file")
    data = read_json(input_file)

    # if no optional feature are given the default is that there are none specified
    if not "optional_features" in data:
        data["optional_features"] = {}

    log.info("Processing attributes")
    for i in data["attributes"]:
        id = re.match("attribute\[(.*)\]", i["id"]).group(1)
        attributes[id] = {}
        attributes[id]["min"] = i["min"]
        attributes[id]["max"] = i["max"]
        attributes[id]["feature"] = re.match("feature\[(.*)\]", i["featureId"]).group(1)
    if data["attributes"]:
        for i in data["configuration"]["attribute_values"]:
            id = re.match("attribute\[(.*)\]", i["id"]).group(1)
            attributes[id]["initial"] = i["value"]
        log.debug(str(attributes))

    log.info("Processing contexts")
    for i in data["contexts"]:
        id = re.match("context\[(.*)\]", i["id"]).group(1)
        contexts[id] = {}
        contexts[id]["min"] = i["min"]
        contexts[id]["max"] = i["max"]
    if data["contexts"]:
        for i in data["configuration"]["context_values"]:
            id = re.match("context\[(.*)\]", i["id"]).group(1)
            contexts[id]["initial"] = i["value"]
    log.debug(str(contexts))

    log.info("Processing initial features, if any")
    if "selectedFeatures" in data["configuration"]:
        for i in data["configuration"]["selectedFeatures"]:
            initial_features.add(re.match("feature\[(.*)\]", i).group(1))
    log.debug(str(initial_features))

    log.info("Processing Constraints")
    if num_of_process > 1:
        # convert in parallel formulas into smt and then parse it here
        # threads can not be used here because antlr parser seems not thread safe
        # the z3 expression can not be serialized
        log.debug("Starting to convert the constraints into smt representation")
        log.debug("Constraint to convert: " + str(len(data["constraints"])))
        pool = multiprocessing.Pool(num_of_process)
        results = pool.map(translate_constraints, [(x,data,features_as_boolean) for x in data["constraints"]])
        log.debug("Converting smt into z3 expressions")
        for smt_f,fs in results:
            constraints += z3.parse_smt2_string(smt_f)
            features.update(fs)
    else:
        for i in data["constraints"]:
            try:
                d = SpecTranslator.translate_constraint(i, data, features_as_boolean)
                log.debug("Find constrataint " + str(d))
                constraints.append(d["formula"])
                features.update(d["features"])
            except Exception as e:
                log.critical("Parsing failed while processing " + i + ": " + str(e))
                log.critical("Exiting")
                sys.exit(1)
    log.info("Constraint processed so far: {}".format(len(constraints)))

    # possibility for reconfigure and explain modality to add directly SMT formulas
    if "smt_constraints" in data:
        log.info("Processing special input constraint modality")
        features.update(data["smt_constraints"]["features"])
        for i in data["smt_constraints"]["formulas"]:
            constraints += z3.parse_smt2_string(i)
            # for explain purposes add smt_constraint to constraints
            data["constraints"].append(i)
    log.info("Constraint processed so far: {}".format(len("constraints")))

    if modality == "reconfigure":
        # SMT formulas direct encoding also for preferences
        # these preferences have the highest priority
        # here we assume that the features are already declared
        if "smt_preferences" in data:
            log.info("Processing special input preferences modality. Pref added as higher priority.")
            for i in data["smt_preferences"]:
                preferences += z3.parse_smt2_string(i)

        log.info("Processing Preferences")
        for i in data["preferences"]:
            try:
                d = SpecTranslator.translate_preference(i, data, features_as_boolean)
                log.debug("Find preference " + str(d))
                preferences.append(d["formula"])
            except Exception as e:
                log.critical("Parsing failed while processing " + i + ": " + str(e))
                log.critical("Exiting")
                sys.exit(1)

    log.info("Processing Context Constraints")
    if "context_constraints" in data:
        for i in data["context_constraints"]:
            try:
                d = SpecTranslator.translate_constraint(i, data, features_as_boolean)
                log.debug("Find context constraint " + str(d))
                contexts_constraints.append(d["formula"])
            except Exception as e:
                log.critical("Parsing failed while processing " + i + ": " + str(e))
                log.critical("Exiting")
                sys.exit(1)

    start_running_time = datetime.datetime.now()
    if modality == "validate":
        import validate_module
        if validate_modality == "grid":
            validate_module.run_validate_grid_search(features, initial_features, contexts, attributes, constraints,
                                     preferences, contexts_constraints, features_as_boolean, non_incremental_solver,
                                     out_stream)
        elif validate_modality == "forall":
            validate_module.run_validate(features, initial_features, contexts, attributes, constraints,
                 preferences, contexts_constraints, features_as_boolean, out_stream)

    elif modality == "explain":
        run_explain(features, contexts, attributes, constraints,
                data, features_as_boolean, constraints_minimization, out_stream)
    elif modality == "check-interface":
        run_check_interface(features, contexts, attributes, constraints, contexts_constraints,
                        read_json(interface_file), features_as_boolean, out_stream)
    elif modality == "check-features":
        import check_features_module
        if check_features_modality == "grid":
            check_features_module.run_feature_analysis_grid_search(
                features,
                features_as_boolean,
                contexts,
                attributes,
                constraints,
                data["optional_features"],
                non_incremental_solver,
                out_stream,
                stop_at_first_anomaly,
                "" if "time_context" not in data else data["time_context"])
        elif check_features_modality == "forall":
            check_features_module.run_feature_analysis_forall(
                features,
                features_as_boolean,
                contexts,
                attributes,
                constraints,
                data["optional_features"],
                non_incremental_solver,
                out_stream,
                stop_at_first_anomaly,
                "" if "time_context" not in data else data["time_context"])
        elif check_features_modality == "pruning":
            check_features_module.run_feature_analysis_with_optimization(
                features,
                features_as_boolean,
                contexts,
                attributes,
                constraints,
                data["optional_features"],
                non_incremental_solver,
                out_stream,
                stop_at_first_anomaly,
                "" if "time_context" not in data else data["time_context"])
    elif modality == "reconfigure":
        run_reconfigure(features, initial_features, contexts, attributes, constraints, preferences,
                        features_as_boolean, timeout, no_default_preferences, out_stream)
    else:
        log.critical("No modality matched. Exiting.")
        sys.exit(1)

    delta = datetime.datetime.now() - start_running_time
    log.info("Seconds taken to run the backend {}".format(delta.total_seconds()))
    delta = datetime.datetime.now() - start_time
    log.info("Seconds taken to run hyvarrec {}".format(delta.total_seconds()))
    log.info("Program Succesfully Ended")


if __name__ == "__main__":
    main()
