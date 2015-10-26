from antlr4 import *
from SpecificationGrammarLexer import SpecificationGrammarLexer
from SpecificationGrammarParser import SpecificationGrammarParser
from SpecificationGrammarVisitor import SpecificationGrammarVisitor


class SpecificationParsingException(Exception):
  
  def __init__(self,value):
    self.value = value
  
  def __str__(self):
    return repr(self.value)

class MyVisitor(SpecificationGrammarVisitor):

  def __init__(self):
    self.parameters = {}
    self.constraints = []
    
  def defaultResult(self):
    return ""
  
  def visitTerminal(self, node):
    
    switcher = {
      'or' : "\\/",
      'and': '/\\',
      'impl': "->",
      'iff' : "<->",
      'xor' : " xor "         
    }
    txt = node.getText()
    if txt in switcher:
      return switcher[txt]
    else:
      return txt
  
  def aggregateResult(self, aggregate, nextResult):
    return aggregate + nextResult
    
  def visitErrorNode(self, node):
    raise SpecificationParsingException("Erroneous Node")

  def visitAdata(self, ctx):
    self.parameters['FEATURE_NUM'] = int(ctx.getChild(1).accept(self))
    self.parameters['CONTEXT_NUM'] = int(ctx.getChild(4).accept(self))
    self.parameters['ATTRIBUTES_NUM'] = ctx.getChild(7).accept(self)
    self.parameters['DOMAIN_ATTRIBUTES'] = ctx.getChild(10).accept(self)
    self.parameters['DOMAIN_CONTEXT'] = ctx.getChild(13).accept(self)
    self.parameters['INITIAL_FEATURES'] = ctx.getChild(16).accept(self)
    self.parameters['INITIAL_ATTRIBUTES'] = ctx.getChild(19).accept(self)
    if ctx.getChildCount() > 20:
      self.constraints = ctx.getChild(21).accept(self)

  def visitAintList(self, ctx):
    num = ctx.getChildCount()
    ls = []
    if num > 2:
      for i in range(1,ctx.getChildCount(),2):
        ls.append(int(ctx.getChild(i).accept(self)))
    return ls

  def visitAconstraintList(self, ctx):
    num = ctx.getChildCount()
    ls = []
    if num > 2:
      for i in range(1,ctx.getChildCount(),2):
        ls.append(ctx.getChild(i).accept(self))
    return ls

  def visitAconstraintBrackets(self, ctx):
    return "( " +  ctx.getChild(1).accept(self) + " )"


  def visitAexprBrackets(self, ctx):
    return "( " +  ctx.getChild(1).accept(self) + " )"
  
  def visitAexprMinus(self, ctx):
    return "-" + ctx.getChild(1).accept(self)
   
  def visitAexprId(self, ctx):
    return ctx.getChild(0).accept(self)
        
  def visitAatomContex(self, ctx):
    return "context[" + str(int(ctx.getChild(1).accept(self)) + 1) + "]"

  def visitAatomFeature(self, ctx):
    return "feat[" + str(int(ctx.getChild(1).accept(self)) + 1) + "]"

  def visitAatomAttribute(self, ctx):
    feat = int(ctx.getChild(1).accept(self))
    attr = int(ctx.getChild(3).accept(self))
    if feat < len(self.parameters['ATTRIBUTES_NUM']):
      for i in range(feat):
        attr += self.parameters['ATTRIBUTES_NUM'][i]
    else:
      raise SpecificationParsingException("number" + str(feat) +
        " is not a valid feature number")
    return "attr[" + str(attr + 1) + "]"
  
#   def visitAstatementPref(self, ctx):
#     ctx.getChild(2).accept(self)
#     return ctx.getChild(0).accept(self)
  
#   def visitAexprLocVariable(self, ctx):
#     loc = ctx.getChild(0).accept(self)
#     num = int(ctx.getChild(2).accept(self))
#     var = ctx.getChild(5).accept(self)
#     if (loc,num) in self.loc_to_int:
#       self.constraints_comp_in_loc = True
#       self.constraints_over_loc = True
#       return "comp_locations[" + str(self.loc_to_int[(loc,num)]) + "," + \
#           var + "]"
#     else:
#       raise SpecificationParsingException(loc + "[" + str(num) +
#          "] is not a valid location")
#     return "" 


def translate_specification(inFile):
  lexer = SpecificationGrammarLexer(FileStream(inFile))
  stream = CommonTokenStream(lexer)
  parser = SpecificationGrammarParser(stream)
  tree = parser.data()
  visitor = MyVisitor()
  visitor.visit(tree)
  return (visitor.parameters, visitor.constraints)
#   
#   s = "constraint " + visitor.visit(tree) + ";\n"
#   s += "constraint symmetry_breaking_constraints("
#   if visitor.constraints_comp_in_loc:
#     s += "true,"
#   else:
#     s += "false,"
#   if visitor.constraints_over_loc:
#     s += "true);\n"
#   else:
#     s += "false);\n"
#   
#   if visitor.preference == []: # default preference -> minimize costs
#     s += "array[1..1] of var int: obj_array;\n"
#     s += "constraint obj_array[1] = sum(l in locations) ( used_locations[l] * costs[l] );"
#   else:
#     s += "array[1.." + str(len(visitor.preference)) + "] of var int: obj_array;\n"
#     for i in range(len(visitor.preference)):
#       s += "constraint obj_array[" + str(i+1) + "] = " +  visitor.preference[i] + ";\n"
#   
#   return (s)