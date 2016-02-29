# Generated from SpecificationGrammar.g4 by ANTLR 4.5.1
from antlr4 import *

# This class defines a complete generic visitor for a parse tree produced by SpecificationGrammarParser.

class SpecificationGrammarVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by SpecificationGrammarParser#constraintPreference.
    def visitConstraintPreference(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#minMaxPreference.
    def visitMinMaxPreference(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#constraint.
    def visitConstraint(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#b_expr.
    def visitB_expr(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#b_term.
    def visitB_term(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#b_factor.
    def visitB_factor(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#relation.
    def visitRelation(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#expr.
    def visitExpr(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#term.
    def visitTerm(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#context.
    def visitContext(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#feature.
    def visitFeature(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#attribute.
    def visitAttribute(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#comparison_op.
    def visitComparison_op(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#boolFact.
    def visitBoolFact(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#bool_binary_op.
    def visitBool_binary_op(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#arith_binary_op.
    def visitArith_binary_op(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#arith_unary_op.
    def visitArith_unary_op(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#unaryOp.
    def visitUnaryOp(self, ctx):
        return self.visitChildren(ctx)


