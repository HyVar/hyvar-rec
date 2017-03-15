"""
This module allows, using eval, to parse a string into a z3 expression
"""
from z3 import *

def get_z3_expression(string,symbols):
    scope = locals()
    for i in symbols:
        scope[i] = Int(i)
    return eval(string,globals(),scope)