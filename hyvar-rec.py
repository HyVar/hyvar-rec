"""
Usage: hyvarRec.py [<options>] <input_file>
  Options:
    -o, --ofile: file where to save the output
    -v, --verbose
    -k, --keep
"""

__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2016, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

import sys, getopt
import os
import logging as log
import shutil
import signal
import psutil
import time
import json

import settings
from solver import Solver
import SpecificationGrammar.SpecTranslator as SpecTranslator

DEVNULL = open(os.devnull, 'wb')

# If KEEP, don't delete temporary files.
KEEP = False

# List of the running solvers.
RUNNING_SOLVERS = []

# List of the temp files.
TMP_FILES = []


#log.basicConfig(filename='example.log',level=log.DEBUG)
#log.basicConfig(level=log.DEBUG)

def usage():
  """Print usage"""
  print(__doc__)

def handler(signum = None, frame = None):
  """
  Handles termination signals.
  """
  log.critical('Signal handler called with signal' + str(signum))
  clean()
  sys.stdout.close()
  sys.exit(signum)

for sig in [signal.SIGTERM, signal.SIGINT, signal.SIGHUP, signal.SIGQUIT]:
  signal.signal(sig, handler)

def send_signal_solver(signal, solver):
  """
  Sends the specified signal to the solver process, and to all its children.
  """
  proc = solver.process
  if proc.poll() is None:
    for p in proc.children(recursive = True):
      try:
        p.send_signal(signal)
      except psutil.NoSuchProcess:
        pass
    try:
      proc.send_signal(signal)
    except psutil.NoSuchProcess:
      pass


  
def clean():
  """
  Utility for (possibly) cleaning temporary files and killing the solvers 
  processes at the end of the solving process (even when the termination is 
  forced externally).
  """
  global RUNNING_SOLVERS
  for solver in RUNNING_SOLVERS:
    send_signal_solver(signal.SIGKILL, solver)
  # Possibly remove temporary files.
  if not KEEP:
    for f in TMP_FILES:
      if os.path.exists(f):
        os.remove(f)


def read_json(json_file): 
  json_data = open(json_file)
  data = json.load(json_data)
  json_data.close()
  return data
      

def generate_dzn(data, dzn_file):
  """
  This procedure generates the dzn file to be used with the mzn program
  """
  with open(dzn_file, 'w') as f:
    
    # compute max and min of domains
    max_int = settings.MAX_INT
    min_int = settings.MIN_INT
    
    for i in data["attributeDomains"]:
      if i["max"] > max_int:
        max_int = i["max"]
      if i["min"] < min_int:
        min_int = i["min"]
  
    for i in data["contextDomains"]:
      if i["max"] > max_int:
        max_int = i["max"]
      if i["min"] < min_int:
        min_int = i["min"]
   
    f.write("MAX_INT = " + str(max_int) + ";\n")
    f.write("MIN_INT = " + str(min_int) + ";\n")
    
    # set the number of features, context, and attributes
    
    f.write("feats = 1.." + str(data["amountOfFeatures"]) + ";\n")
    f.write("contexts = 1.." + str(data["amountOfContexts"]) + ";\n")
    f.write("attrs = 1.." + str(sum(data["attributesPerFeature"])) + ";\n")
    
    # set the domains arrays
    ls = map (lambda x: x["min"], data["contextDomains"])
    f.write("context_min = " + str(ls) + ";\n")
    
    ls = map (lambda x: x["max"], data["contextDomains"])
    f.write("context_max = " + str(ls) + ";\n")
    
    ls = map (lambda x: x["min"], data["attributeDomains"])
    f.write("attr_min = " + str(ls) + ";\n")

    ls = map (lambda x: x["max"], data["attributeDomains"])
    f.write("attr_max = " + str(ls) + ";\n")
    
    # set the initial value arrays
    f.write("init_feat = " + str(data["configuration"]["selectedFeatures"]) + ";\n")
    f.write("init_attr = " + str(data["configuration"]["attributeValues"]) + ";\n")
    f.write("init_context = " + str(data["configuration"]["contextValues"]) + ";\n")


def generata_mzn(constraints, preferences, mzn_file):
  """
  This procedure adds the constraints and the preferences at the end of the mzn file
  """
  with open(mzn_file, 'a') as outfile:
    for i in constraints:
      outfile.write("constraint " + i + ";\n") 
    
    outfile.write("array [1.." + str(len(preferences) + 2) + "] of var int: obj_array;\n")
    counter = 1
    for i in preferences:
      outfile.write("constraint obj_array[" + str(counter) + "] = " + i + ";\n")
      counter += 1
    outfile.write("constraint obj_array[" + str(counter) + "] = sum(f in feats) (diff_feat[f]);\n")
    counter += 1
    outfile.write("constraint obj_array[" + str(counter) + "] = sum(a in attrs) (diff_attr[a]);\n")


def get_json_solution(buf):
  sol = ""
  ls = buf.split("\n")
  # if there is a solution print it in json format
  # solution looks like
  # features = [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0]
  # attributes = [200]
  # %OBJVAR [0, 0, 0, 1, 1, 200, 0, 0] 
  if len(ls) > 1:
    sol = "{"
    for line in ls:
      if line.startswith("features ="):
        sol += line. replace('features =','"selectedFeatures":') + ","
      if line.startswith("attributes ="):
        sol += line. replace('attributes =','"attributeValues":')
    sol += "}"
  json_sol = json.loads(sol)
  json_sol["optimality"] = 0
  return json_sol
    

def main(argv):
  """Main procedure """   
  output_file = ""
  
  try:
    opts, args = getopt.getopt(argv,"ho:vk",["help","ofile=","verbose","keep"])
  except getopt.GetoptError as err:
    print str(err)
    usage()
    sys.exit(1)
  for opt, arg in opts:
    if opt == '-h':
      usage()
      sys.exit()
    elif opt in ("-o", "--ofile"):
      output_file = arg
    elif opt in ("-k", "--keep"):
      global KEEP
      KEEP = True
    elif opt in ("-v", "--verbose"):
      log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
      log.info("Verbose output.")
  
  if len(args) != 1:
    print "one arguments is required"
    usage()
    sys.exit(1)
    
  input_file = args[0]
  out_stream = sys.stdout
  if output_file:
    out_stream = open(output_file, "w") 
   
  script_directory = os.path.dirname(os.path.realpath(__file__))
    
  input_file = os.path.abspath(input_file)
  
  pid = str(os.getpgid(0))
  mzn_file = "/tmp/" + pid + ".mzn"
  dzn_file = "/tmp/" + pid + ".dzn"
  
  global TMP_FILES
  TMP_FILES = [ mzn_file , dzn_file ]
 
  constraints = []
  preferences = []
  log.info("Reading input file")
  data = read_json(input_file)
  log.info("Processing Constraints")
  for i in data["constraints"]:
    try:
      constraints.append(SpecTranslator.translate_constraint(i,data))   
    except Exception as e:
      log.critical("Parsing failed while processing " + i + ": " + str(e))
      log.critical("Exiting")
      sys.exit(1)
  log.debug("****Constraints****")
  log.debug(str(constraints))
  log.info("Processing Preferences")
  for i in data["preferences"]:
    try:
      preferences.append(SpecTranslator.translate_preference(i,data))   
    except Exception as e:
      log.critical("Parsing failed while processing " + i + ": " + str(e))
      log.critical("Exiting")
      sys.exit(1)
  log.debug("****Preferences****")
  log.debug(str(preferences))
  
  log.info("Generating dzn file")
  generate_dzn(data, dzn_file)
  
  log.info("Copy mzn file and add FM constraints and preferences")
  shutil.copyfile(script_directory + "/minizinc_prog.mzn", mzn_file)
  generata_mzn(constraints, preferences, mzn_file)
         
  log.info("Running solvers")
  
  global RUNNING_SOLVERS
  RUNNING_SOLVERS = [
     Solver("default", mzn_file, dzn_file, "", "gecode") ]
   
  for i in RUNNING_SOLVERS:
    i.run()
   
  ended = False
  json_sol = ""
  while not ended and RUNNING_SOLVERS:
    time.sleep(settings.SLEEP_TIME) 
    for i in RUNNING_SOLVERS:
      sol = i.get_solution()
      if sol != "":
        json_sol = get_json_solution(sol)
        json.dump(json_sol,out_stream)
        out_stream.write("\n")
        out_stream.flush()
      if i.is_ended():
        if json_sol != "":
          json_sol["optimality"] = 1
          json.dump(json_sol,out_stream)
        log.info("Search completed by " + i.get_id())
        ended = True
        continue
    # TODO print solution only if it is better       
      if i.process.poll() is not None:
        log.info("Solver " + i.get_id() + " terminated with code " + 
                 str(i.process.returncode))
        log.debug("****Solver " + i.get_id() + " stderr*****")
        log.debug(i.process.stderr.readlines())
        log.debug("****Solver " + i.get_id() + " stderr*****")
        RUNNING_SOLVERS.remove(i)         
     
  log.info("Clean.")
  clean()    
  log.info("Program Succesfully Ended")


if __name__ == "__main__":
  main(sys.argv[1:])