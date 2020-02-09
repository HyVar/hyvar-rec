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
from subprocess import Popen, PIPE
import time

import importlib

__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2016, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.2"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

# timeout in seconds
TIMEOUT = 3600

script_directory = os.path.dirname(os.path.realpath(__file__))

def read_json(json_file):
    json_data = open(json_file)
    data = json.load(json_data)
    json_data.close()
    return data


def main(argv):

    try:
        opts, args = getopt.getopt(argv, "hv", ["help","verbose"])
    except getopt.GetoptError as err:
        print(str(err))
        print(__doc__)
        sys.exit(1)
    for opt, arg in opts:
        if opt in ('-h', "--help"):
            print(__doc__)
            sys.exit()
        elif opt in ("-v", "--verbose"):
            logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
            logging.info("Verbose output.")

    if len(args) != 1:
        print("one arguments is required")
        print(__doc__)
        sys.exit(1)

    directory = os.path.abspath(args[0])
    temp_file = "/tmp/hyvarrec_output.json"
    temp_file_4explain = "/tmp/hyvarrec_output_explain.json"

    jsons = sorted([f for f in os.listdir(directory) if os.path.isfile(os.path.join(directory, f)) and f[-5:] == ".json"])

    sum_time = 0
    max = 0
    min = TIMEOUT
    count = 0
    results = {}
    time_results = {}

    for i in jsons:
        logging.debug("Processing " + i)
        start_time = time.time()
        proc = Popen(["timeout", str(TIMEOUT), "python", "../hyvar-rec.py","-o", temp_file,
                      os.path.join(directory, i)],
                     cwd=script_directory, stdout=PIPE, stderr=PIPE)
        # proc = Popen(["timeout", unicode(TIMEOUT), "python", "../hyvar-rec.py", "--validate", "-o", temp_file,
        #       os.path.join(directory, i)],
        #      cwd=script_directory, stdout=PIPE, stderr=PIPE)
        out, err = proc.communicate()
        elapsed_time = time.time() - start_time
        logging.debug('Stdout')
        logging.debug(out)
        logging.debug('Stderr')
        logging.debug(err)
        logging.debug('Return code:' + str(proc.returncode))

        data_out = read_json(temp_file)
        data_in = read_json(os.path.join(directory, i))

        # to test hyvar-rec in explain modality
        # if proc.returncode != 124:
        #     if data_out["result"] == "not_valid":
        #         data_in["configuration"]["context_values"] = [{"id": "context[" + x["id"] + "]", "value": int(x["value"])}
        #                                                        for x in data_out["contexts"]]
        #         with open(temp_file_4explain, "w") as f:
        #             json.dump(data_in,f)
        #         start_time = time.time()
        #         proc = Popen(["timeout", unicode(TIMEOUT), "python", "../hyvar-rec.py", "--explain", "-o", temp_file,
        #                       temp_file_4explain],
        #                      cwd=script_directory, stdout=PIPE, stderr=PIPE)
        #         out, err = proc.communicate()
        #         elapsed_time_4explain = time.time() - start_time
        #         logging.debug('Stdout')
        #         logging.debug(out)
        #         logging.debug('Stderr')
        #         logging.debug(err)
        #         logging.debug('Return code:' + unicode(proc.returncode))
        #         data = read_json(temp_file)
        #         print data["result"] + ",",
        #     else:
        #         elapsed_time_4explain = 0
        #         print "not_run_valid,",
        # else:
        #     elapsed_time_4explain = -1
        #     print "not_run_timeout,",


        count += 1
        sum_time += elapsed_time
        if elapsed_time > max:
            max = elapsed_time
        if elapsed_time < min:
            min = elapsed_time

        if proc.returncode == 0:
            logging.debug('Output of hyvar-rec')
            logging.debug(str(data_out))
            if data_out["result"] in results:
                results[data_out["result"]] += 1
                time_results[data_out["result"]] += elapsed_time
            else:
                results[data_out["result"]] = 1
                time_results[data_out["result"]] = elapsed_time
        elif proc.returncode == 124:
            if "timeout" in results:
                results["timeout"] += 1
            else:
                results["timeout"] = 1
                time_results["timeout"] = None
        else:
            if "error" in results:
                results["error"] += 1
            else:
                results["error"] = 1
                time_results["error"] = None

        print(i + "," + str(elapsed_time) + "," + data_out["result"], end=' ')
        # to test hyvar-rec in explain modality, comment the line otherwise
        # print "," + unicode(len(data_in["contexts"])) + "," + unicode(elapsed_time_4explain),
        print("," + str(len(data_in["constraints"])), end=' ')
        print("")

    print("Results," + \
        str(count) + "," + \
        str(sum_time/count) + "," + \
        str(max) + "," + \
        str(min) + "," + \
        ",".join([x + "," + str(results[x]) + "," + str(time_results[x]) for x in sorted(results.keys())]))

if __name__ == "__main__":
    main(sys.argv[1:])
