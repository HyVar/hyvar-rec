"""
This module allows, using eval, to parse a string into a z3 expression
"""
from z3 import *

def get_z3_expression(string,symbols):
    scope = locals()
    for i in symbols:
        scope[i] = Int(i)
    v = eval(string,globals(),scope)
    if v == True:
        return BoolVal(True)
    elif v == False:
        return BoolVal(False)
    else:
        return v