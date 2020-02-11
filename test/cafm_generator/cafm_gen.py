#!/usr/bin/python

__author__     = "Jacopo Mauro"
__copyright__  = "Copyright 2019-2020, Jacopo Mauro"
__license__    = "ICS"
__version__    = "1"
__maintainer__ = "Jacopo Mauro"
__email__      = "mauro.jacopo@gmail.com"
__status__     = "Prototype"

# This tool is a proof of concept based on the
# [Power-Law Random SAT Generator](https://github.com/RalfRothenberger/Power-Law-Random-SAT-Generator)
# tool that can generate random SAT constraints

import click
import subprocess
import tempfile
import shutil
import json

template = {
    "attributes": [],
    "contexts": [],
    "constraints": [],
    "preferences":[],
    "configuration":{"context_values": []},
    "optional_features": {},
    "smt_constraints": {"formulas": [], "features": [] },
}

def var_to_smt(n,c):
    if n > 0:
        if n > c:
            return f"f{n}"
        else:
            return f"(= 1 c{n})"
    else:
        if n < -c:
            return f"(not f{-n})"
        else:
            return f"(= 0 c{-n})"

def var_to_declare(n,c):
    if n > 0:
        if n > c:
            return f"(declare-fun f{n} () Bool)"
        else:
            return f"(declare-fun c{n} () Int)"
    else:
        if n < -c:
            return f"(declare-fun f{-n} () Bool)"
        else:
            return f"(declare-fun c{-n} () Int)"

@click.command()
@click.option('--num-of-features', '-f', type=click.INT, default=90,
              help='Number of features.', show_default=True)
@click.option('--num-of-contexts', '-c', type=click.INT, default=10,
              help='Number of context.', show_default=True)
@click.option('--ratio', '-r', type=click.FLOAT, default=4.26,
              help='Ratio of constraints for number of features (clause having all context will be removed)', show_default=True)
@click.option('--seed', '-s', type=click.INT, default=0,
              help='seed for the generation', show_default=True)
@click.option('--sat-gen-cmd', type=click.STRING, default="CreateSAT",
              help='Number of context.', show_default=True)
@click.option('--output-file', '-o',
              type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True),
              help='Output file', default="cafm_example.json", show_default=True)
def main(num_of_features,
         num_of_contexts,
         ratio,
         output_file,
         sat_gen_cmd,
         seed):

    tmpdir = tempfile.mkdtemp()

    # define context, initially all to false
    for i in range(num_of_contexts):
        template["contexts"].append({"id": f"context[c{i+1}]", "min": 0, "max": 1})
        template["configuration"]["context_values"].append({"id": f"context[c{i+1}]", "value": 0})

    # all features are optional
    for i in range(num_of_features):
        template["optional_features"][f"f{i+num_of_contexts+1}"]= []

    cmd = [sat_gen_cmd,
           "-g", "u", # uniform distribution
           "-v", f"{num_of_features + num_of_contexts}",
           "-c", f"{int(ratio*num_of_features)}",
           "-k", "3",
           # "-p", "2.5",
           "-u", "1",
           "-f", f"{tmpdir}/gen",
           "-s", f"{seed}"]
    process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = process.communicate()

    with open(f"{tmpdir}/gen.cnf", 'r') as f:
        lines = f.readlines()
    shutil.rmtree(tmpdir, ignore_errors=True)

    lines = [[int(i) for i in line.split(' ')[:-1]] for line in lines[1:]]
    # remove those having only context
    lines = [x for x in lines if not all([y < num_of_contexts for y in x])]
    template["smt_constraints"]["features"] = [f"f{x + num_of_contexts+1}" for x in range(num_of_features)]
    for i in lines:
        formula = " ".join([var_to_declare(x,num_of_contexts) for x in i]) + "(assert (or "
        formula += " ".join([var_to_smt(x,num_of_contexts) for x in i]) + "))"
        template["smt_constraints"]["formulas"].append(formula)
    with open(output_file, 'w') as f:
        json.dump(template, f, indent=2)


if __name__ == "__main__":
    main()
