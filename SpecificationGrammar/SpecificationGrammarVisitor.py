# Generated from SpecificationGrammar.g4 by ANTLR 4.5.1
from antlr4 import *

# This class defines a complete generic visitor for a parse tree produced by SpecificationGrammarParser.

class SpecificationGrammarVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by SpecificationGrammarParser#Adata.
    def visitAdata(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AintList.
    def visitAintList(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AconstraintList.
    def visitAconstraintList(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AconstraintBrackets.
    def visitAconstraintBrackets(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AconstraintBool1Op.
    def visitAconstraintBool1Op(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AboolFact.
    def visitAboolFact(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AconstraintBool2Op.
    def visitAconstraintBool2Op(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AconstraintExpression.
    def visitAconstraintExpression(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AexprArithmetic.
    def visitAexprArithmetic(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AexprMinus.
    def visitAexprMinus(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AexprBrackets.
    def visitAexprBrackets(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AexprInt.
    def visitAexprInt(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AexprId.
    def visitAexprId(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AatomContex.
    def visitAatomContex(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AatomFeature.
    def visitAatomFeature(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#AatomAttribute.
    def visitAatomAttribute(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#op.
    def visitOp(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#arithmetic_op.
    def visitArithmetic_op(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#bool2Op.
    def visitBool2Op(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#bool1Op.
    def visitBool1Op(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#boolFact.
    def visitBoolFact(self, ctx):
        return self.visitChildren(ctx)


