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
TIMEOUT = 60

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
        print str(err)
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
        print "one arguments is required"
        print(__doc__)
        sys.exit(1)

    directory = os.path.abspath(args[0])
    temp_file = "/tmp/hyvarrec_output.json"

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
        proc = Popen(["timeout",unicode(TIMEOUT),"python","../hyvar-rec.py","-o",temp_file,os.path.join(directory, i)],
                         cwd=script_directory, stdout=PIPE, stderr=PIPE)
        out, err = proc.communicate()
        elapsed_time = time.time() - start_time
        logging.debug('Stdout of JSON cost annotations extractor')
        logging.debug(out)
        logging.debug('Stderr of JSON cost annotations extractor')
        logging.debug(err)
        logging.debug('Return code:' + unicode(proc.returncode))

        count += 1
        sum_time += elapsed_time
        if elapsed_time > max:
            max = elapsed_time
        if elapsed_time < min:
            min = elapsed_time

        if proc.returncode == 0:
            data = read_json(temp_file)
            logging.debug('Output of hyvar-rec')
            logging.debug(unicode(data))
            if data["result"] in results:
                results[data["result"]] += 1
                time_results[data["result"]] += elapsed_time
            else:
                results[data["result"]] = 1
                time_results[data["result"]] = elapsed_time
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

        print i + "," + unicode(elapsed_time) + "," + data["result"]

    print "Results," + \
        unicode(count) + "," + \
        unicode(sum_time/count) + "," + \
        unicode(max) + "," + \
        unicode(min) + "," + \
        ",".join([x + "," + unicode(results[x]) + "," + unicode(time_results[x]) for x in sorted(results.keys())])

if __name__ == "__main__":
    main(sys.argv[1:])
