"""
SpecTranslator.py: program that defines the function to parse the constraints
and preferences and translate them into a minizinc formalism
"""
__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2016, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

from antlr4 import *
from .SpecificationGrammarLexer import SpecificationGrammarLexer
from .SpecificationGrammarParser import SpecificationGrammarParser
from .SpecificationGrammarVisitor import SpecificationGrammarVisitor
import z3


class MyVisitor(SpecificationGrammarVisitor):
    def __init__(self, json_data, feature_as_boolean=False):
        """the input parameter for the visitor is the json data"""
        self.json_data = json_data
        self.features = set()
        self.attributes = set()
        self.contexts = set()
        self.feature_as_boolean = feature_as_boolean

    def defaultResult(self):
        return ""

    def visitTerminal(self, node):
        return node.getText()

    def aggregateResult(self, aggregate, next_result):
        return next_result

    def visitErrorNode(self, node):
        token = node.getSymbol()
        raise Exception("Erroneous Node at line " +
                        str(token.line) + ", column " + str(token.column) + ": '" +
                        str(token.text) + "'")

    def visitConstraintPreference(self, ctx):
        formula = ctx.getChild(0).accept(self)
        if isinstance(formula,z3.BoolRef):
            return z3.If(z3.simplify(ctx.getChild(0).accept(self)),1,0)
        return z3.simplify(ctx.getChild(0).accept(self))

    def visitMinMaxPreference(self, ctx):
        op = ctx.getChild(0).accept(self)
        attribute = ctx.getChild(3).accept(self)
        if op == "min":
            return z3.simplify(0 - z3.Int(attribute))
        return z3.Int(attribute)

    def visitConstraint(self, ctx):
        return ctx.getChild(0).accept(self)

    def visitB_expr(self, ctx):
        formula = ctx.getChild(0).accept(self)
        for i in range(1, ctx.getChildCount(), 2):
            op = ctx.getChild(i).accept(self)
            f = ctx.getChild(i + 1).accept(self)
            if op == "and":
                formula = z3.And(formula, f)
            elif op == "or":
                formula = z3.Or(formula, f)
            elif op == "impl":
                formula = z3.Implies(formula, f)
            elif op == "iff":
                formula = z3.simplify(z3.And(z3.Implies(formula, f), z3.Implies(f,formula)))
                #formula = z3.simplify(formula == f)
            elif op == "xor":
                formula = z3.simplify((z3.And(z3.Implies(formula, z3.Not(f)), z3.Implies(z3.Not(formula),f))))
                #formula = z3.simplify(formula == z3.Not(f))
            else:
                raise Exception("Boolean operator " + op + "not recognised")
        return formula

    def visitB_term(self, ctx):
        formula = ctx.getChild(ctx.getChildCount() - 1).accept(self)
        if ctx.getChildCount() > 1:
            return z3.Not(formula)
        return formula

    def visitBFactorOneOnly(self, ctx):
        formulas = []
        for i in range(2,ctx.getChildCount()-1,2):
            formulas.append(ctx.getChild(i).accept(self))
        if not formulas:
            return z3.BoolVal(False)
        elif len(formulas) == 1:
            return formulas[0]
        return z3.PbEq([(i,1) for i in formulas],1)

    def visitRelation(self, ctx):
        formula = ctx.getChild(0).accept(self)
        for i in range(1, ctx.getChildCount(), 2):
            op = ctx.getChild(i).accept(self)
            f = ctx.getChild(i + 1).accept(self)
            if op == "<=":
                formula = z3.simplify(formula <= f)
            elif op == "=":
                formula = z3.simplify(formula == f)
            elif op == ">=":
                formula = z3.simplify(formula >= f)
            elif op == "<":
                formula = z3.simplify(formula < f)
            elif op == ">":
                formula = z3.simplify(formula > f)
            elif op == "!=":
                formula = z3.simplify(formula != f)
            else:
                raise Exception("Comparison operator " + op + "not recognised")
        return formula

    def visitExpr(self, ctx):
        formula = ctx.getChild(0).accept(self)
        num = ctx.getChildCount()
        if num == 1 and self.feature_as_boolean:
            return formula
        for i in range(1, num, 2):
            op = ctx.getChild(i).accept(self)
            f = ctx.getChild(i + 1).accept(self)
            if isinstance(formula, z3.BoolRef):
                formula = z3.If(formula, 1, 0)
            if isinstance(f, z3.BoolRef):
                f = z3.If(f,1,0)
            if op == "+":
                formula = z3.simplify(formula + f)
            elif op == "-":
                formula = z3.simplify(formula - f)
            elif op == "*":
                formula = z3.simplify(formula * f)
            else:
                raise Exception("Arithmetic operator " + op + "not recognised")
        return formula

    def visitTermInt(self, ctx):
        return z3.IntVal(int(ctx.getChild(0).accept(self)))

    def visitTermContext(self, ctx):
        id = ctx.getChild(1).accept(self)
        self.contexts.add(id)
        return z3.Int(id)

    def visitTermFeature(self, ctx):
        id = ctx.getChild(1).accept(self)
        self.features.add(id)
        if self.feature_as_boolean:
            return z3.Bool(id)
        return z3.Int(id)

    def visitTermAttribute(self, ctx):
        id = ctx.getChild(1).accept(self)
        self.attributes.add(id)
        return z3.Int(id)

    def visitTermBrackets(self, ctx):
        return ctx.getChild(1).accept(self)

    def visitBoolFact(self, ctx):
        fact = ctx.getChild(0).accept(self)
        if fact == "true":
            return z3.simplify(z3.BoolVal(True))
        return z3.simplify(z3.BoolVal(False))


def translate_constraint(in_string, data,feature_as_boolean=False):
    lexer = SpecificationGrammarLexer(InputStream(in_string))
    stream = CommonTokenStream(lexer)
    parser = SpecificationGrammarParser(stream)
    tree = parser.constraint()
    visitor = MyVisitor(data,feature_as_boolean)
    formula = visitor.visit(tree)
    return {
        "formula": formula,
        "contexts": visitor.contexts,
        "features": visitor.features,
        "attributes": visitor.attributes}


def translate_preference(in_string, data, feature_as_boolean=False):
    lexer = SpecificationGrammarLexer(InputStream(in_string))
    stream = CommonTokenStream(lexer)
    parser = SpecificationGrammarParser(stream)
    tree = parser.preference()
    visitor = MyVisitor(data,feature_as_boolean)
    formula = visitor.visit(tree)
    return {
        "formula": formula,
        "contexts": visitor.contexts,
        "features": visitor.features,
        "attributes": visitor.attributes}
