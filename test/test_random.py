"""
Program to run hyvarrec on all the files contained in a directory reporting their running times
Usage:
  test_dir.py <directory containing the json files>
"""
import getopt
import sys
import logging
import os
import datetime
import json
import subprocess
import time
import click
import tempfile
import shutil

import importlib

__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2016, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.2"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

# timeout in seconds
TIMEOUT = 300
DOCKERIMAGE="jacopomauro/hyvar-rec"

CONTEXTS = [10]
FEATURES = [500]
# FEATURES = [500,750]
RATIOS = [4.26]
# RATIOS = [4.2,4.3,4.4,4.5]
REPETITIONS = 1
RETESTS = 1


def run_hyvar(text, tempdir, cmd, infile, outfile):
    start_time = time.time()
    docker_cmd = f"timeout {TIMEOUT} docker run --rm -v {tempdir}:/mydir {DOCKERIMAGE} python hyvar-rec.py".split(" ") \
                 + cmd.split(" ") + [infile]
    logging.debug(f"Running command: {' '.join(docker_cmd)}")
    process = subprocess.Popen(docker_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = process.communicate()
    elapsed_time = time.time() - start_time
    logging.debug(f"Return code: {process.returncode}")
    logging.debug(f"Stdout: {stdout}")
    logging.debug(f"Stderror: {stderr}")

    out = f"{text};{cmd};"
    if process.returncode == 0:
        try:
            data = json.loads(stdout)
            out += f"{elapsed_time};{json.dumps(data)}"
        except:
            out += "ErrorJson;"
    elif process.returncode == 124:
        out += f"Timeout{TIMEOUT};"
    else:
        out += f"Error{process.returncode};"
    out += "\n"

    with open(outfile, "a") as f:
        f.write(out)


@click.command()
@click.option('--verbose', '-v', count=True,
              help="Print debug messages.")
@click.option('--output-file', '-o',
              type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True),
              help='Output file - Otherwise the output is printed on stdout.', default="out.csv")
def main(verbose,
         output_file,
         ):

    log_level = logging.ERROR
    if verbose == 1:
        log_level = logging.WARNING
    elif verbose == 2:
        log_level = logging.INFO
    elif verbose >= 3:
        log_level = logging.DEBUG
    logging.basicConfig(format="[%(asctime)s][%(levelname)s][%(name)s]%(message)s",level=log_level)
    logging.info("Verbose Level: " + str(verbose))

    # generate the random files
    tempdir = tempfile.mkdtemp()

    # head of csv file
    with open(output_file, "a") as f:
        f.write(f"features;contexts;ratio;i;j;seed;cmd;time;result")

    for f in FEATURES:
        for c in CONTEXTS:
            for r in RATIOS:
                for i in range(REPETITIONS):
                    # generate random json file
                    cmd = f"python /hyvar-rec/test/cafm_generator/cafm_gen.py -f {f} -c {c} -r {r} -o /mydir/{f}_{c}_{r}_{i}.json -s {i}"
                    docker_cmd = (f"docker run --rm -v {tempdir}:/mydir {DOCKERIMAGE} " + cmd).split(" ")
                    logging.debug(f"Run command: {' '.join(docker_cmd)}")
                    process = subprocess.Popen(docker_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                    stdout, stderr = process.communicate()

                    for j in range(RETESTS):
                        info = f"{f};{c};{r};{i};{j};"
                        input_file = f"/mydir/{f}_{c}_{r}_{i}.json"
                        cmd = f"--features-as-boolean --validate --validate-modality forall"
                        run_hyvar(info, tempdir, cmd, input_file, output_file)

                        cmd = f"--features-as-boolean --validate --validate-modality grid"
                        run_hyvar(info, tempdir, cmd, input_file, output_file)

                        cmd = f"--features-as-boolean --check-features --check-features-modality grid --stop-at-first-anomaly"
                        run_hyvar(info, tempdir, cmd, input_file, output_file)

                        cmd = f"--features-as-boolean --check-features --check-features-modality forall --stop-at-first-anomaly"
                        run_hyvar(info, tempdir, cmd, input_file, output_file)

                        cmd = f"--features-as-boolean --check-features --check-features-modality pruning --stop-at-first-anomaly"
                        run_hyvar(info, tempdir, cmd, input_file, output_file)
    shutil.rmtree(tempdir)


if __name__ == "__main__":
    main()
