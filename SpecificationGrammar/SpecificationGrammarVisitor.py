# Generated from SpecificationGrammar.g4 by ANTLR 4.7.2
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .SpecificationGrammarParser import SpecificationGrammarParser
else:
    from SpecificationGrammarParser import SpecificationGrammarParser

# This class defines a complete generic visitor for a parse tree produced by SpecificationGrammarParser.

class SpecificationGrammarVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by SpecificationGrammarParser#constraintPreference.
    def visitConstraintPreference(self, ctx:SpecificationGrammarParser.ConstraintPreferenceContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#minMaxPreference.
    def visitMinMaxPreference(self, ctx:SpecificationGrammarParser.MinMaxPreferenceContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#constraint.
    def visitConstraint(self, ctx:SpecificationGrammarParser.ConstraintContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#b_expr.
    def visitB_expr(self, ctx:SpecificationGrammarParser.B_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#b_term.
    def visitB_term(self, ctx:SpecificationGrammarParser.B_termContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#bFactorFact.
    def visitBFactorFact(self, ctx:SpecificationGrammarParser.BFactorFactContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#bFactorRelation.
    def visitBFactorRelation(self, ctx:SpecificationGrammarParser.BFactorRelationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#bFactorOneOnly.
    def visitBFactorOneOnly(self, ctx:SpecificationGrammarParser.BFactorOneOnlyContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#relation.
    def visitRelation(self, ctx:SpecificationGrammarParser.RelationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#expr.
    def visitExpr(self, ctx:SpecificationGrammarParser.ExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#termInt.
    def visitTermInt(self, ctx:SpecificationGrammarParser.TermIntContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#termContext.
    def visitTermContext(self, ctx:SpecificationGrammarParser.TermContextContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#termFeature.
    def visitTermFeature(self, ctx:SpecificationGrammarParser.TermFeatureContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#termAttribute.
    def visitTermAttribute(self, ctx:SpecificationGrammarParser.TermAttributeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#termBrackets.
    def visitTermBrackets(self, ctx:SpecificationGrammarParser.TermBracketsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#boolFact.
    def visitBoolFact(self, ctx:SpecificationGrammarParser.BoolFactContext):
        return self.visitChildren(ctx)



del SpecificationGrammarParser