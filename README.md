# hyvar-rec

hyvar-rec allows to reconfigure an existing SPL subject to contextual
changes.

Given an existing product with its features and attributes it first
checks if the product is valid according to the current context.
If not it tries to compute a new set of features and attributes that the new
product should support.

hyvar-rec uses MiniZinc Search and in particular the Gecode solver to solve
the optimization problems involved in the reconfiguration. Other solver could
be easily supported.


Requirements:

 - Python 2.7
 - antlr4 module for python
 - MiniZinc Search (http://www.minizinc.org/minisearch/)


