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
    if line.startswith("%"):
      sol = line + "\n" + sol
    else:     
      if not find:
        if line.startswith("----------"):
          find = True
        else:
          buf += line + "\n"
      if find:
        if line.startswith("----------"):
          continue
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
  
  def __init__(self, solver, mzn_file, dzn_file, id):
    self.solver = solver
    self.mzn_file = mzn_file
    self.dzn_file = dzn_file
    self.id = id
  
  def run(self):
    
    stdlib_path = settings.MZN_STDLIB_PATH
    if not stdlib_path:
      # retrieve the PATH of the "--stdlib-dir"
      for path in os.getenv("PATH").split(os.path.pathsep):
          full_path = path + os.sep + settings.MINISEARCH_COMMAND
          if os.path.exists(full_path):
            stdlib_path = os.path.dirname(full_path)[:-3] + "share" + os.sep + "minizinc"
      
    self.process = Popen( [settings.MINISEARCH_COMMAND,
          "--stdlib-dir", stdlib_path,
          #"--solver", self.solver,
          self.mzn_file, self.dzn_file], stdout=PIPE, stderr=PIPE )
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
    return self.id