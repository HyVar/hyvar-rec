from antlr4 import *
from SpecificationGrammarLexer import SpecificationGrammarLexer
from SpecificationGrammarParser import SpecificationGrammarParser
from SpecificationGrammarVisitor import SpecificationGrammarVisitor


class MyVisitor(SpecificationGrammarVisitor):

  def __init__(self, json_data):
    "the input parameter for the visitor is the json data"
    self.json_data = json_data
    
    
  def defaultResult(self):
    return ""
  
  
  def visitTerminal(self, node):
    
    switcher = {
      'or' : "\\/",
      'and': '/\\',
      'impl': "->",
      'iff' : "<->"  
    }
    txt = node.getText()
    if txt in switcher:
      return switcher[txt]
    else:
      return txt
  
  
  def aggregateResult(self, aggregate, nextResult):
    return aggregate + " " + nextResult
    
  
  def visitErrorNode(self, node):
    token = node.getSymbol()
    raise Exception("Erroneous Node at line "  +
            str(token.line) + ", column " + str(token.column) + ": '" + 
            str(token.text) + "'"  )


  def visitConstraintPreference(self, ctx):
    return "bool2int(" +ctx.getChild(0).accept(self) + ")"


  def visitMinMaxPreference(self, ctx):
    op = ctx.getChild(0).accept(self)
    attribute = ctx.getChild(2).accept(self)
    if op == "min":
      return "- " + attribute
    return attribute


  def visitConstraint(self, ctx):
    return ctx.getChild(0).accept(self)

        
  def visitContex(self, ctx):
    return "context[" + str(int(ctx.getChild(1).accept(self)) + 1) + "]"


  def visitFeature(self, ctx):
    return "feat[" + str(int(ctx.getChild(1).accept(self)) + 1) + "]"

  
  def visitAttribute(self, ctx):
    feat = int(ctx.getChild(1).accept(self))
    attr = int(ctx.getChild(3).accept(self))
    # compute the real number of attribute according to the array of the 
    # feature attributes
    if feat < len(self.json_data["attributesPerFeature"]):
      for i in range(feat):
        attr += self.json_data["attributesPerFeature"][i]
    else:
      raise Exception("number" + str(feat) +
        " is not a valid feature number")
    return "attr[" + str(attr + 1) + "]"


def translate_constraint(in_string, data):
  lexer = SpecificationGrammarLexer(InputStream(in_string))
  stream = CommonTokenStream(lexer)
  parser = SpecificationGrammarParser(stream)
  tree = parser.constraint()
  visitor = MyVisitor(data)
  return visitor.visit(tree)


def translate_preference(in_string,data):  
  lexer = SpecificationGrammarLexer(InputStream(in_string))
  stream = CommonTokenStream(lexer)
  parser = SpecificationGrammarParser(stream)
  tree = parser.preference()
  visitor = MyVisitor(data)
  return visitor.visit(tree)

