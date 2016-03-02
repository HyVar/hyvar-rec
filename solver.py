""" Module for better handling the execution of a solver """
__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2016, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

from subprocess import Popen,PIPE
import fcntl
import settings
import os


def read_lines(proc):
  """
  Returns the stream of the read lines of a process.
  """
  try:
    return proc.stdout.read()
  except:
    return ''
  
def get_last_solution(buf):
  lines = buf.split("\n")
  lines.reverse()
  buf = ""
  sol = ""
  end = False
  
  find = False
  for line in lines:
    if line.startswith("=========="):
      end = True
    if not find:
      if line.startswith("----------"):
        find = True
      else:
        buf += line + "\n"
    else:
      if line.startswith("----------"):
        break
      else:
        sol = line + "\n" + sol
  return (sol,buf,end)
  


class Solver:
  
  # Contains the buffer having partial solutions
  buf = ""
  
  # Object of class psutil.Popen referring to the solving process.
  process = None
  
  # True if solver has explored the entire search space
  ended = False
  
  # Stderr of the process
  err = None
  
  def __init__(self, solver, mzn_file, dzn_file, globals_dir, id_string):
    self.solver = solver
    self.mzn_file = mzn_file
    self.dzn_file = dzn_file
    self.global_dir = globals_dir
    self.id_string = id_string
  
  def run(self):
    
    stdlib_path = settings.MZN_STDLIB_PATH
    if not stdlib_path:
      # retrieve the PATH of the "--stdlib-dir"
      for path in os.getenv("PATH").split(os.path.pathsep):
          full_path = path + os.sep + settings.MINISEARCH_COMMAND
          if os.path.exists(full_path):
            # check if the stdlib is in ../share/minizinc as installed by default
            last_dir = path.split(os.sep)[-1]
            stdlib_path = path.replace(last_dir, os.sep + "share" + os.sep + "minizinc")
            if not os.path.exists(stdlib_path):
              raise Exception("Minizinc stdlib path not found - Please provide it in settings.py")
      
    if self.solver == "default":
      cmd = [settings.MINISEARCH_COMMAND,
          "--stdlib-dir", stdlib_path,
          self.mzn_file, self.dzn_file]
    else:
      cmd = [settings.MINISEARCH_COMMAND,
          "--stdlib-dir", stdlib_path,
          "--solver", self.solver,
          "-I", self.globals_dir,
          self.mzn_file, self.dzn_file]
    
    self.process = Popen( cmd, stdout=PIPE, stderr=PIPE )
    # For non-blocking read.
    fd = self.process.stdout.fileno()
    fl = fcntl.fcntl(fd, fcntl.F_GETFL)
    fcntl.fcntl(fd, fcntl.F_SETFL, fl | os.O_NONBLOCK)
    
  def get_solution(self):
    self.buf += read_lines(self.process)
    # Sometimes not all the lines are read from solver output.
    if self.process.poll() is not None:
      self.buf += read_lines(self.process)
    sol, self.buf, ended = get_last_solution(self.buf) 
    if ended:
      self.ended = True
    return sol
  
  def is_ended(self):
    return self.ended
  
  def get_id(self):
    return self.id_string
