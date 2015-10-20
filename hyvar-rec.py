"""
Usage: hyvarRec.py [<options>] <input_file> <context file>
  Options:
    -o, --ofile: file where to save the output
    -v, --verbose
    -k, --keep
"""

import sys, getopt
import os
import logging as log
import shutil
import signal
import psutil
import time

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


def read_context(context_file):
  ls = []
  with open(context_file, 'r') as f:
    for i in f.readlines():
      try:
        ls.append(int(i))
      except ValueError:
        pass
  return ls
      

def generate_dzn(parameters, constraints, init_context, dzn_file):
 
  with open(dzn_file, 'w') as f:
    
    # compute max and min of domains
    max_int = settings.MAX_INT
    min_int = settings.MIN_INT
    
    for i in parameters['DOMAIN_ATTRIBUTES']:
      if i > max_int:
        max_int = i
      if i < min_int:
        min_int = i
  
    for i in parameters['DOMAIN_CONTEXT']:
      if i > max_int:
        max_int = i
      if i < min_int:
        min_int = i
   
    f.write("MAX_INT = " + str(max_int) + ";\n")
    f.write("MIN_INT = " + str(min_int) + ";\n")
    
    # set the number of features, context, and attributes
    
    f.write("feats = 1.." + str(parameters['FEATURE_NUM']) + ";\n")
    f.write("contexts = 1.." + str(parameters['CONTEXT_NUM']) + ";\n")
    f.write("attrs = 1.." + str(sum(parameters['ATTRIBUTES_NUM'])) + ";\n")
    
    # set the domains arrays
    ls = map (lambda x: parameters['DOMAIN_CONTEXT'][x],
              range(0,len(parameters['DOMAIN_CONTEXT']),2))
    f.write("context_min = " + str(ls) + ";\n")
    
    ls = map (lambda x: parameters['DOMAIN_CONTEXT'][x+1],
              range(0,len(parameters['DOMAIN_CONTEXT']),2))
    f.write("context_max = " + str(ls) + ";\n")
    
    ls = map (lambda x: parameters['DOMAIN_ATTRIBUTES'][x],
              range(0,len(parameters['DOMAIN_ATTRIBUTES']),2))
    f.write("attr_min = " + str(ls) + ";\n")

    ls = map (lambda x: parameters['DOMAIN_ATTRIBUTES'][x+1],
              range(0,len(parameters['DOMAIN_ATTRIBUTES']),2))
    f.write("attr_max = " + str(ls) + ";\n")
    
    # set the initial value arrays
    f.write("init_feat = " + str(parameters['INITIAL_FEATURES']) + ";\n")
    f.write("init_attr = " + str(parameters['INITIAL_ATTRIBUTES']) + ";\n")
    f.write("init_context = " + str(init_context) + ";\n")


def print_solution(buf,out):  
  if buf.startswith("%VALID") or buf.startswith("%RECOMPUTING"):
    out.write(buf)
    out.write("----------\n")
  else:
    out.write(buf)
    
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
      KEEP = True
    elif opt in ("-v", "--verbose"):
      log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
      log.info("Verbose output.")
  
  if len(args) != 2:
    print "2 arguments are required"
    usage()
    sys.exit(1)
    
  input_file = args[0]
  contex_file = args[1]
  out_stream = sys.stdout
  if output_file:
    out_stream = open(output_file, "w") 
   
  script_directory = os.path.dirname(os.path.realpath(__file__))
    
  input_file = os.path.abspath(input_file)
  contex_file = os.path.abspath(contex_file)
  
  pid = str(os.getpgid(0))
  mzn_file = "/tmp/" + pid + ".mzn"
  dzn_file = "/tmp/" + pid + ".dzn"
  
  TMP_FILES = [ mzn_file , dzn_file ]
 
  log.info("Processing specification")
  try:
    parameters, constraints = SpecTranslator.translate_specification(input_file)
  except SpecTranslator.SpecificationParsingException as e:
    log.critical("Parsing of the specification failed: " + e.value)
    log.critical("Exiting")
    sys.exit(1)
  
  log.debug("****Parameters****")
  log.debug(str(parameters))
  log.debug("****Constraints****")
  log.debug(str(constraints))
  
  log.info("Reading context file")
  context = read_context(contex_file)
  log.debug("****Context****")
  log.debug(str(context))

  
  log.info("Generating dzn file")
  generate_dzn(parameters, constraints, context, dzn_file)
  
  log.info("Copy mzn file and add FM constraints")
  shutil.copyfile(script_directory + "/minizinc_prog.mzn", mzn_file)
  with open(mzn_file, 'a') as outfile:
    for i in constraints:
      outfile.write("constraint " + i + ";\n") 
       
  log.info("Running solvers")
   
  RUNNING_SOLVERS = [
    Solver("gecode", mzn_file, dzn_file, "gecode") ]
   
  for i in RUNNING_SOLVERS:
    i.run()
   
  ended = False
  while not ended and RUNNING_SOLVERS:
    time.sleep(settings.SLEEP_TIME) 
    for i in RUNNING_SOLVERS:
      sol = i.get_solution()
      if sol != "":
        # TODO print solution only if it is better
        print_solution(sol, out_stream)
      if i.is_ended():
        log.info("Search completed by " + i.get_id())
        ended = True
        out_stream.write("==========\n")
        continue
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