"""
Usage: hyvarRec.py [<options>] <input_file>
  Options:
    -h, --help: to print the usage message
    -o, --ofile: STRING file where to save the output
    -v, --verbose: activate verbose mode
    -k, --keep: keep auxiliary files generated during the computation
    -p, --par_parse: INT processes generated to parse the constraints
    --validate: activate the validation mode to check if for all context the FM is not void
    --explain: try to explain why a FM is void
    --check-interface: checks if the interface given as additional file is a proper interface
"""

__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2016, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.2"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

import sys, getopt
import os
import logging as log
import json
import re
import multiprocessing

import z3

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


def reconfigure(
        features,
        initial_features,
        contexts,
        attributes,
        constraints,
        preferences,
        out_stream):
    """Perform the reconfiguration task
    """
    solver = z3.Optimize()
    log.info("Add variables")
    for i in features:
        solver.add(0 <= z3.Int(i), z3.Int(i) <= 1)
    for i in attributes.keys():
        solver.add(attributes[i]["min"] <= z3.Int(i), z3.Int(i) <= attributes[i]["max"])
    for i in contexts.keys():
        solver.add(contexts[i]["min"] <= z3.Int(i), z3.Int(i) <= contexts[i]["max"])

    log.info("Enforce context to be equal to intial values")
    for i in contexts.keys():
        solver.add(contexts[i]["initial"] == z3.Int(i))

    log.info("Add constraints")
    for i in constraints:
        solver.add(i)

    log.info("Add preferences")
    for i in preferences:
        solver.minimize(i)

    log.info("Add preference: minimize the number of initial features removed")
    if initial_features:
        solver.maximize(z3.Sum([z3.Int(i) for i in initial_features]))

    log.info("Add preference: minimize the number of attributes changed")
    initial_attributes = [k for k in attributes.keys() if "initial" in attributes[k]]
    if initial_attributes:
        solver.maximize(
            z3.Sum([z3.If(z3.Int(i) == z3.IntVal(attributes[i]["initial"]), 1, 0) for i in initial_attributes]))

    log.info("Add preference: minimize the number of non initial features added")
    if features.difference(initial_features):
        solver.minimize(z3.Sum([z3.Int(i) for i in features.difference(initial_features)]))
    log.debug(unicode(solver))

    log.info("Computing reconfiguration")
    result = solver.check()

    log.info("Printing output")
    if result == z3.sat:
        model = solver.model()
        out = {"result": "sat", "features": [], "attributes": []}
        for i in features:
            if model[z3.Int(i)] == z3.IntVal(1):
                out["features"].append(i)
        for i in attributes.keys():
            if attributes[i]["feature"] in out["features"]:
                out["attributes"].append({"id": i, "value": unicode(model[z3.Int(i)])})
        json.dump(out, out_stream)
        out_stream.write("\n")
    else:
        out_stream.write('{"result": "unsat"}\n')


def validate(
        features,
        initial_features,
        contexts,
        attributes,
        constraints,
        preferences,
        context_constraints,
        out_stream):
    """Perform the validation task
    """
    solver = z3.Solver()

    log.info("Add context variables")
    for i in contexts.keys():
        solver.add(contexts[i]["min"] <= z3.Int(i), z3.Int(i) <= contexts[i]["max"])

    log.info("Add contexts constraints")
    for i in context_constraints:
        solver.add(i)

    log.info("Building the FM formula")
    formulas = []
    for i in features:
        formulas.append(0 <= z3.Int(i))
        formulas.append(z3.Int(i) <= 1)

    for i in attributes.keys():
        formulas.append(attributes[i]["min"] <= z3.Int(i))
        formulas.append(z3.Int(i) <= attributes[i]["max"])

    for i in constraints:
        formulas.append(i)

    log.info("Add forall not FM formula")
    solver.add(z3.ForAll(
        [z3.Int(i) for i in features ] + [z3.Int(i) for i in attributes.keys()],
        z3.Not(z3.And(formulas))
    ))
    log.debug(solver)

    log.info("Computing")
    result = solver.check()
    log.info("Printing output")

    if result == z3.sat:
        model = solver.model()
        out = {"result": "not_valid", "contexts": []}
        for i in contexts.keys():
            out["contexts"].append({"id": i, "value": unicode(model[z3.Int(i)])})
        json.dump(out, out_stream)
        out_stream.write("\n")
    else:
        out_stream.write('{"result":"valid"}\n')


def explain(
        features,
        initial_features,
        contexts,
        attributes,
        constraints,
        preferences,
        data,
        out_stream):
    """Get the explanation of the unsat of the FM model
    """
    solver = z3.Solver()
    solver.set(unsat_core=True)

    log.info("Add variables")
    for i in features:
        solver.add(0 <= z3.Int(i), z3.Int(i) <= 1)
    for i in attributes.keys():
        solver.add(attributes[i]["min"] <= z3.Int(i), z3.Int(i) <= attributes[i]["max"])
    for i in contexts.keys():
        solver.add(contexts[i]["min"] <= z3.Int(i), z3.Int(i) <= contexts[i]["max"])

    log.info("Enforce context to be equal to initial values")
    for i in contexts.keys():
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
        for i in features:
            if model[z3.Int(i)] == z3.IntVal(1):
                out["features"].append(i)
        for i in attributes.keys():
            if attributes[i]["feature"] in out["features"]:
                out["attributes"].append({"id": i, "value": unicode(model[z3.Int(i)])})
        json.dump(out, out_stream)
        out_stream.write("\n")
    else:
        core = solver.unsat_core()
        log.debug("Core: " + unicode(core))
        out = {"result": "unsat", "constraints": []}
        for i in range(len(constraints)):
            if z3.Bool('aux' + str(i)) in core:
                out["constraints"].append(data["constraints"][i])
        json.dump(out, out_stream)
        out_stream.write("\n")


def check_interface(features, contexts, attributes, constraints, contexts_constraints,
                interface, out_stream):
    """Check if the interface given is a proper interface
    """
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
    log.debug(unicode(attributes))

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
    log.debug(unicode(contexts))

    log.info("Processing Constraints")
    for i in interface["constraints"]:
        try:
            d = SpecTranslator.translate_constraint(i, interface)
            log.debug("Find constraint " + unicode(d))
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
                d = SpecTranslator.translate_constraint(i, interface)
                log.debug("Find context constraint " + unicode(d))
                i_contexts_constraints.append(d["formula"])
            except Exception as e:
                log.critical("Parsing failed while processing " + i + ": " + str(e))
                log.critical("Exiting")
                sys.exit(1)

    log.info("Checking Context Constraints Extensibility")
    solver = z3.Solver()
    for i in contexts.keys():
        solver.add(contexts[i]["min"] <= z3.Int(i))
        solver.add(z3.Int(i) <= contexts[i]["max"])
    solver.add(z3.And(i_contexts_constraints))
    solver.add(z3.Not(z3.And(contexts_constraints)))
    result = solver.check()

    if result == z3.sat:
        model = solver.model()
        out = {"result": "not_valid: context extensibility problem", "contexts": []}
        for i in contexts.keys():
            out["contexts"].append({"id": i, "value": unicode(model[z3.Int(i)])})
        json.dump(out, out_stream)
        out_stream.write("\n")

    solver = z3.Solver()

    log.info("Add interface variables")
    for i in i_features:
        solver.add(0 <= z3.Int(i), z3.Int(i) <= 1)
    for i in i_attributes.keys():
        solver.add(i_attributes[i]["min"] <= z3.Int(i), z3.Int(i) <= i_attributes[i]["max"])
    for i in i_contexts.keys():
        solver.add(i_contexts[i]["min"] <= z3.Int(i), z3.Int(i) <= i_contexts[i]["max"])

    log.info("Add interface contexts constraints")
    solver.add(z3.And(i_contexts_constraints))
    solver.add(z3.And(contexts_constraints))

    log.info("Add interface constraints")
    for i in i_constraints:
        solver.add(i)

    log.info("Add FM context variables")
    for i in contexts.keys():
        if i not in i_contexts:
            solver.add(contexts[i]["min"] <= z3.Int(i))
            solver.add(z3.Int(i) <= contexts[i]["max"])

    log.info("Building the FM formula")
    formulas = []
    for i in features:
        if i not in i_features:
            formulas.append(0 <= z3.Int(i))
            formulas.append(z3.Int(i) <= 1)
    for i in attributes.keys():
        if i not in i_attributes:
            formulas.append(attributes[i]["min"] <= z3.Int(i))
            formulas.append(z3.Int(i) <= attributes[i]["max"])
    for i in constraints:
        formulas.append(i)

    log.info("Add forall fatures and attributes not formula")
    solver.add(z3.ForAll(
        [z3.Int(i) for i in features if i not in i_features] +
        [z3.Int(i) for i in attributes.keys() if i not in i_attributes.keys()],
        z3.Not(z3.And(formulas))
    ))
    log.debug(solver)

    log.info("Computing")
    result = solver.check()
    log.info("Printing output")

    if result == z3.sat:
        model = solver.model()
        out = {"result": "not_valid", "contexts": [], "attributes": [], "features" : []}
        for i in contexts.keys():
            out["contexts"].append({"id": i, "value": unicode(model[z3.Int(i)])})
        for i in i_features:
            out["features"].append({"id": i, "value": unicode(model[z3.Int(i)])})
        for i in i_attributes.keys():
            out["attributes"].append({"id": i, "value": unicode(model[z3.Int(i)])})
        json.dump(out, out_stream)
        out_stream.write("\n")
    else:
        out_stream.write('{"result":"valid"}\n')


def translate_constraints(pair):
    c,data = pair
    try:
        d = SpecTranslator.translate_constraint(c, data)
    except Exception as e:
        log.critical("Parsing failed while processing " + c + ": " + str(e))
        log.critical("Exiting")
        sys.exit(1)
    return d["formula"],d["features"]



def main(argv):
    """Main procedure """
    output_file = ""
    modality = "" # default modality is to proceed with the reconfiguration
    interface_file = ""
    num_of_process = 1

    try:
        opts, args = getopt.getopt(argv, "ho:vkp:", ["help", "ofile=", "verbose", "keep", "validate", "explain", "check-interface=","par_parse="])
    except getopt.GetoptError as err:
        print str(err)
        usage()
        sys.exit(1)
    for opt, arg in opts:
        if opt in ('-h', "--help"):
            usage()
            sys.exit()
        elif opt in ("-o", "--ofile"):
            output_file = arg
        elif opt in ("-k", "--keep"):
            global KEEP
            KEEP = True
        elif opt == "--validate":
            modality = "validate"
        elif opt == "--explain":
            modality = "explain"
        elif opt == "--check-interface":
            modality = "check-interface"
            interface_file = os.path.abspath(arg)
            assert arg > 0
        elif opt in ("-p", "--par_parse"):
            num_of_process = int(arg)
        elif opt in ("-v", "--verbose"):
            log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
            log.info("Verbose output.")

    if len(args) != 1:
        print "one arguments is required"
        usage()
        sys.exit(1)

    input_file = os.path.abspath(args[0])
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

    log.info("Processing attributes")
    for i in data["attributes"]:
        id = re.match("attribute\[(.*)\]", i["id"]).group(1)
        attributes[id] = {}
        attributes[id]["min"] = i["min"]
        attributes[id]["max"] = i["max"]
        attributes[id]["feature"] = re.match("feature\[(.*)\]", i["featureId"]).group(1)
    for i in data["configuration"]["attribute_values"]:
        id = re.match("attribute\[(.*)\]", i["id"]).group(1)
        attributes[id]["initial"] = i["value"]
    log.debug(unicode(attributes))

    log.info("Processing contexts")
    for i in data["contexts"]:
        id = re.match("context\[(.*)\]", i["id"]).group(1)
        contexts[id] = {}
        contexts[id]["min"] = i["min"]
        contexts[id]["max"] = i["max"]
    for i in data["configuration"]["context_values"]:
        id = re.match("context\[(.*)\]", i["id"]).group(1)
        contexts[id]["initial"] = i["value"]
    log.debug(unicode(contexts))

    log.info("Processing initial features")
    for i in data["configuration"]["selectedFeatures"]:
        initial_features.add(re.match("feature\[(.*)\]", i).group(1))
    log.debug(unicode(initial_features))

    log.info("Processing Constraints")
    if num_of_process > 1:
        pool = multiprocessing.Pool(num_of_process)
        pool.map(translate_constraints, [(x, data) for x in data["constraints"]])
        result = pool.get()
        for c,fs in result:
            constraints.append(c)
            features.update(fs)
    else:
        for i in data["constraints"]:
            try:
                d = SpecTranslator.translate_constraint(i, data)
                log.debug("Find constrataint " + unicode(d))
                constraints.append(d["formula"])
                features.update(d["features"])
            except Exception as e:
                log.critical("Parsing failed while processing " + i + ": " + str(e))
                log.critical("Exiting")
                sys.exit(1)

    # possibility for reconfigure and explain modality to add directly SMT formulas
    if "smt_constraints" in data:
        log.info("Processing special input constraint modality")
        features.update(data["smt_constraints"]["features"])
        for i in data["smt_constraints"]["formulas"]:
            constraints.append(z3.parse_smt2_string(i))
            # for explain purposes add smt_constraint to constraints
            data["constraints"].append(i)

    log.info("Processing Preferences")
    for i in data["preferences"]:
        try:
            d = SpecTranslator.translate_preference(i, data)
            log.debug("Find preference " + unicode(d))
            preferences.append(d["formula"])
        except Exception as e:
            log.critical("Parsing failed while processing " + i + ": " + str(e))
            log.critical("Exiting")
            sys.exit(1)

    log.info("Processing Context Constraints")
    if "context_constraints" in data:
        for i in data["context_constraints"]:
            try:
                d = SpecTranslator.translate_constraint(i, data)
                log.debug("Find context constraint " + unicode(d))
                contexts_constraints.append(d["formula"])
            except Exception as e:
                log.critical("Parsing failed while processing " + i + ": " + str(e))
                log.critical("Exiting")
                sys.exit(1)

    if modality == "validate":
        validate(features, initial_features, contexts, attributes, constraints,
                 preferences, contexts_constraints, out_stream)
    elif modality == "explain":
        explain(features, initial_features, contexts, attributes, constraints,
                 preferences, data, out_stream)
    elif modality == "check-interface":
        check_interface(features, contexts, attributes, constraints, contexts_constraints,
                        read_json(interface_file), out_stream)
    else:
        reconfigure(features, initial_features, contexts, attributes, constraints, preferences, out_stream)

    log.info("Program Succesfully Ended")


if __name__ == "__main__":
    main(sys.argv[1:])
