# Generated from SpecificationGrammar.g4 by ANTLR 4.7
# encoding: utf-8
from __future__ import print_function
from antlr4 import *
from io import StringIO
import sys

def serializedATN():
    with StringIO() as buf:
        buf.write(u"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3")
        buf.write(u"\"^\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4")
        buf.write(u"\b\t\b\4\t\t\t\4\n\t\n\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3")
        buf.write(u"\2\5\2\35\n\2\3\3\3\3\3\3\3\4\3\4\3\4\7\4%\n\4\f\4\16")
        buf.write(u"\4(\13\4\3\5\5\5+\n\5\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6")
        buf.write(u"\3\6\7\6\66\n\6\f\6\16\69\13\6\3\6\3\6\5\6=\n\6\3\7\3")
        buf.write(u"\7\3\7\5\7B\n\7\3\b\3\b\3\b\7\bG\n\b\f\b\16\bJ\13\b\3")
        buf.write(u"\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3")
        buf.write(u"\t\5\tZ\n\t\3\n\3\n\3\n\2\2\13\2\4\6\b\n\f\16\20\22\2")
        buf.write(u"\7\3\2\24\25\4\2\13\r\22\23\3\2\27\34\3\2\35\37\3\2\20")
        buf.write(u"\21\2`\2\34\3\2\2\2\4\36\3\2\2\2\6!\3\2\2\2\b*\3\2\2")
        buf.write(u"\2\n<\3\2\2\2\f>\3\2\2\2\16C\3\2\2\2\20Y\3\2\2\2\22[")
        buf.write(u"\3\2\2\2\24\35\5\4\3\2\25\26\t\2\2\2\26\27\7\3\2\2\27")
        buf.write(u"\30\7\4\2\2\30\31\7 \2\2\31\32\7\5\2\2\32\33\7\6\2\2")
        buf.write(u"\33\35\7\2\2\3\34\24\3\2\2\2\34\25\3\2\2\2\35\3\3\2\2")
        buf.write(u"\2\36\37\5\6\4\2\37 \7\2\2\3 \5\3\2\2\2!&\5\b\5\2\"#")
        buf.write(u"\t\3\2\2#%\5\b\5\2$\"\3\2\2\2%(\3\2\2\2&$\3\2\2\2&\'")
        buf.write(u"\3\2\2\2\'\7\3\2\2\2(&\3\2\2\2)+\7\17\2\2*)\3\2\2\2*")
        buf.write(u"+\3\2\2\2+,\3\2\2\2,-\5\n\6\2-\t\3\2\2\2.=\5\22\n\2/")
        buf.write(u"=\5\f\7\2\60\61\7\16\2\2\61\62\7\7\2\2\62\67\5\6\4\2")
        buf.write(u"\63\64\7\b\2\2\64\66\5\6\4\2\65\63\3\2\2\2\669\3\2\2")
        buf.write(u"\2\67\65\3\2\2\2\678\3\2\2\28:\3\2\2\29\67\3\2\2\2:;")
        buf.write(u"\7\5\2\2;=\3\2\2\2<.\3\2\2\2</\3\2\2\2<\60\3\2\2\2=\13")
        buf.write(u"\3\2\2\2>A\5\16\b\2?@\t\4\2\2@B\5\16\b\2A?\3\2\2\2AB")
        buf.write(u"\3\2\2\2B\r\3\2\2\2CH\5\20\t\2DE\t\5\2\2EG\5\20\t\2F")
        buf.write(u"D\3\2\2\2GJ\3\2\2\2HF\3\2\2\2HI\3\2\2\2I\17\3\2\2\2J")
        buf.write(u"H\3\2\2\2KZ\7!\2\2LM\7\t\2\2MN\7 \2\2NZ\7\5\2\2OP\7\n")
        buf.write(u"\2\2PQ\7 \2\2QZ\7\5\2\2RS\7\4\2\2ST\7 \2\2TZ\7\5\2\2")
        buf.write(u"UV\7\3\2\2VW\5\6\4\2WX\7\6\2\2XZ\3\2\2\2YK\3\2\2\2YL")
        buf.write(u"\3\2\2\2YO\3\2\2\2YR\3\2\2\2YU\3\2\2\2Z\21\3\2\2\2[\\")
        buf.write(u"\t\6\2\2\\\23\3\2\2\2\n\34&*\67<AHY")
        return buf.getvalue()


class SpecificationGrammarParser ( Parser ):

    grammarFileName = "SpecificationGrammar.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ u"<INVALID>", u"'('", u"'attribute['", u"']'", u"')'", 
                     u"'['", u"','", u"'context['", u"'feature['", u"'and'", 
                     u"'or'", u"'xor'", u"'oneonly'", u"'not'", u"'true'", 
                     u"'false'", u"'impl'", u"'iff'", u"'min'", u"'max'", 
                     u"'abs'", u"'<='", u"'='", u"'>='", u"'<'", u"'>'", 
                     u"'!='", u"'+'", u"'-'", u"'*'" ]

    symbolicNames = [ u"<INVALID>", u"<INVALID>", u"<INVALID>", u"<INVALID>", 
                      u"<INVALID>", u"<INVALID>", u"<INVALID>", u"<INVALID>", 
                      u"<INVALID>", u"AND", u"OR", u"XOR", u"ONEONLY", u"NOT", 
                      u"TRUE", u"FALSE", u"IMPL", u"IFF", u"MIN", u"MAX", 
                      u"ABS", u"LEQ", u"EQ", u"GEQ", u"LT", u"GT", u"NEQ", 
                      u"PLUS", u"MINUS", u"TIMES", u"ID", u"INT", u"WS" ]

    RULE_preference = 0
    RULE_constraint = 1
    RULE_b_expr = 2
    RULE_b_term = 3
    RULE_b_factor = 4
    RULE_relation = 5
    RULE_expr = 6
    RULE_term = 7
    RULE_boolFact = 8

    ruleNames =  [ u"preference", u"constraint", u"b_expr", u"b_term", u"b_factor", 
                   u"relation", u"expr", u"term", u"boolFact" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    T__2=3
    T__3=4
    T__4=5
    T__5=6
    T__6=7
    T__7=8
    AND=9
    OR=10
    XOR=11
    ONEONLY=12
    NOT=13
    TRUE=14
    FALSE=15
    IMPL=16
    IFF=17
    MIN=18
    MAX=19
    ABS=20
    LEQ=21
    EQ=22
    GEQ=23
    LT=24
    GT=25
    NEQ=26
    PLUS=27
    MINUS=28
    TIMES=29
    ID=30
    INT=31
    WS=32

    def __init__(self, input, output=sys.stdout):
        super(SpecificationGrammarParser, self).__init__(input, output=output)
        self.checkVersion("4.7")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None



    class PreferenceContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.PreferenceContext, self).__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_preference

     
        def copyFrom(self, ctx):
            super(SpecificationGrammarParser.PreferenceContext, self).copyFrom(ctx)



    class ConstraintPreferenceContext(PreferenceContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.PreferenceContext)
            super(SpecificationGrammarParser.ConstraintPreferenceContext, self).__init__(parser)
            self.copyFrom(ctx)

        def constraint(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.ConstraintContext,0)


        def accept(self, visitor):
            if hasattr(visitor, "visitConstraintPreference"):
                return visitor.visitConstraintPreference(self)
            else:
                return visitor.visitChildren(self)


    class MinMaxPreferenceContext(PreferenceContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.PreferenceContext)
            super(SpecificationGrammarParser.MinMaxPreferenceContext, self).__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(SpecificationGrammarParser.ID, 0)
        def EOF(self):
            return self.getToken(SpecificationGrammarParser.EOF, 0)
        def MIN(self):
            return self.getToken(SpecificationGrammarParser.MIN, 0)
        def MAX(self):
            return self.getToken(SpecificationGrammarParser.MAX, 0)

        def accept(self, visitor):
            if hasattr(visitor, "visitMinMaxPreference"):
                return visitor.visitMinMaxPreference(self)
            else:
                return visitor.visitChildren(self)



    def preference(self):

        localctx = SpecificationGrammarParser.PreferenceContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_preference)
        self._la = 0 # Token type
        try:
            self.state = 26
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [SpecificationGrammarParser.T__0, SpecificationGrammarParser.T__1, SpecificationGrammarParser.T__6, SpecificationGrammarParser.T__7, SpecificationGrammarParser.ONEONLY, SpecificationGrammarParser.NOT, SpecificationGrammarParser.TRUE, SpecificationGrammarParser.FALSE, SpecificationGrammarParser.INT]:
                localctx = SpecificationGrammarParser.ConstraintPreferenceContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 18
                self.constraint()
                pass
            elif token in [SpecificationGrammarParser.MIN, SpecificationGrammarParser.MAX]:
                localctx = SpecificationGrammarParser.MinMaxPreferenceContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 19
                _la = self._input.LA(1)
                if not(_la==SpecificationGrammarParser.MIN or _la==SpecificationGrammarParser.MAX):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 20
                self.match(SpecificationGrammarParser.T__0)
                self.state = 21
                self.match(SpecificationGrammarParser.T__1)
                self.state = 22
                self.match(SpecificationGrammarParser.ID)
                self.state = 23
                self.match(SpecificationGrammarParser.T__2)
                self.state = 24
                self.match(SpecificationGrammarParser.T__3)
                self.state = 25
                self.match(SpecificationGrammarParser.EOF)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class ConstraintContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.ConstraintContext, self).__init__(parent, invokingState)
            self.parser = parser

        def b_expr(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.B_exprContext,0)


        def EOF(self):
            return self.getToken(SpecificationGrammarParser.EOF, 0)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_constraint

        def accept(self, visitor):
            if hasattr(visitor, "visitConstraint"):
                return visitor.visitConstraint(self)
            else:
                return visitor.visitChildren(self)




    def constraint(self):

        localctx = SpecificationGrammarParser.ConstraintContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_constraint)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 28
            self.b_expr()
            self.state = 29
            self.match(SpecificationGrammarParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class B_exprContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.B_exprContext, self).__init__(parent, invokingState)
            self.parser = parser

        def b_term(self, i=None):
            if i is None:
                return self.getTypedRuleContexts(SpecificationGrammarParser.B_termContext)
            else:
                return self.getTypedRuleContext(SpecificationGrammarParser.B_termContext,i)


        def AND(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.AND)
            else:
                return self.getToken(SpecificationGrammarParser.AND, i)

        def OR(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.OR)
            else:
                return self.getToken(SpecificationGrammarParser.OR, i)

        def IMPL(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.IMPL)
            else:
                return self.getToken(SpecificationGrammarParser.IMPL, i)

        def IFF(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.IFF)
            else:
                return self.getToken(SpecificationGrammarParser.IFF, i)

        def XOR(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.XOR)
            else:
                return self.getToken(SpecificationGrammarParser.XOR, i)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_b_expr

        def accept(self, visitor):
            if hasattr(visitor, "visitB_expr"):
                return visitor.visitB_expr(self)
            else:
                return visitor.visitChildren(self)




    def b_expr(self):

        localctx = SpecificationGrammarParser.B_exprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_b_expr)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 31
            self.b_term()
            self.state = 36
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while (((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.AND) | (1 << SpecificationGrammarParser.OR) | (1 << SpecificationGrammarParser.XOR) | (1 << SpecificationGrammarParser.IMPL) | (1 << SpecificationGrammarParser.IFF))) != 0):
                self.state = 32
                _la = self._input.LA(1)
                if not((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.AND) | (1 << SpecificationGrammarParser.OR) | (1 << SpecificationGrammarParser.XOR) | (1 << SpecificationGrammarParser.IMPL) | (1 << SpecificationGrammarParser.IFF))) != 0)):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 33
                self.b_term()
                self.state = 38
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class B_termContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.B_termContext, self).__init__(parent, invokingState)
            self.parser = parser

        def b_factor(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.B_factorContext,0)


        def NOT(self):
            return self.getToken(SpecificationGrammarParser.NOT, 0)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_b_term

        def accept(self, visitor):
            if hasattr(visitor, "visitB_term"):
                return visitor.visitB_term(self)
            else:
                return visitor.visitChildren(self)




    def b_term(self):

        localctx = SpecificationGrammarParser.B_termContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_b_term)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 40
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==SpecificationGrammarParser.NOT:
                self.state = 39
                self.match(SpecificationGrammarParser.NOT)


            self.state = 42
            self.b_factor()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class B_factorContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.B_factorContext, self).__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_b_factor

     
        def copyFrom(self, ctx):
            super(SpecificationGrammarParser.B_factorContext, self).copyFrom(ctx)



    class BFactorRelationContext(B_factorContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.B_factorContext)
            super(SpecificationGrammarParser.BFactorRelationContext, self).__init__(parser)
            self.copyFrom(ctx)

        def relation(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.RelationContext,0)


        def accept(self, visitor):
            if hasattr(visitor, "visitBFactorRelation"):
                return visitor.visitBFactorRelation(self)
            else:
                return visitor.visitChildren(self)


    class BFactorFactContext(B_factorContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.B_factorContext)
            super(SpecificationGrammarParser.BFactorFactContext, self).__init__(parser)
            self.copyFrom(ctx)

        def boolFact(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.BoolFactContext,0)


        def accept(self, visitor):
            if hasattr(visitor, "visitBFactorFact"):
                return visitor.visitBFactorFact(self)
            else:
                return visitor.visitChildren(self)


    class BFactorOneOnlyContext(B_factorContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.B_factorContext)
            super(SpecificationGrammarParser.BFactorOneOnlyContext, self).__init__(parser)
            self.copyFrom(ctx)

        def ONEONLY(self):
            return self.getToken(SpecificationGrammarParser.ONEONLY, 0)
        def b_expr(self, i=None):
            if i is None:
                return self.getTypedRuleContexts(SpecificationGrammarParser.B_exprContext)
            else:
                return self.getTypedRuleContext(SpecificationGrammarParser.B_exprContext,i)


        def accept(self, visitor):
            if hasattr(visitor, "visitBFactorOneOnly"):
                return visitor.visitBFactorOneOnly(self)
            else:
                return visitor.visitChildren(self)



    def b_factor(self):

        localctx = SpecificationGrammarParser.B_factorContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_b_factor)
        self._la = 0 # Token type
        try:
            self.state = 58
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [SpecificationGrammarParser.TRUE, SpecificationGrammarParser.FALSE]:
                localctx = SpecificationGrammarParser.BFactorFactContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 44
                self.boolFact()
                pass
            elif token in [SpecificationGrammarParser.T__0, SpecificationGrammarParser.T__1, SpecificationGrammarParser.T__6, SpecificationGrammarParser.T__7, SpecificationGrammarParser.INT]:
                localctx = SpecificationGrammarParser.BFactorRelationContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 45
                self.relation()
                pass
            elif token in [SpecificationGrammarParser.ONEONLY]:
                localctx = SpecificationGrammarParser.BFactorOneOnlyContext(self, localctx)
                self.enterOuterAlt(localctx, 3)
                self.state = 46
                self.match(SpecificationGrammarParser.ONEONLY)
                self.state = 47
                self.match(SpecificationGrammarParser.T__4)
                self.state = 48
                self.b_expr()
                self.state = 53
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while _la==SpecificationGrammarParser.T__5:
                    self.state = 49
                    self.match(SpecificationGrammarParser.T__5)
                    self.state = 50
                    self.b_expr()
                    self.state = 55
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)

                self.state = 56
                self.match(SpecificationGrammarParser.T__2)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class RelationContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.RelationContext, self).__init__(parent, invokingState)
            self.parser = parser

        def expr(self, i=None):
            if i is None:
                return self.getTypedRuleContexts(SpecificationGrammarParser.ExprContext)
            else:
                return self.getTypedRuleContext(SpecificationGrammarParser.ExprContext,i)


        def LEQ(self):
            return self.getToken(SpecificationGrammarParser.LEQ, 0)

        def EQ(self):
            return self.getToken(SpecificationGrammarParser.EQ, 0)

        def GEQ(self):
            return self.getToken(SpecificationGrammarParser.GEQ, 0)

        def LT(self):
            return self.getToken(SpecificationGrammarParser.LT, 0)

        def GT(self):
            return self.getToken(SpecificationGrammarParser.GT, 0)

        def NEQ(self):
            return self.getToken(SpecificationGrammarParser.NEQ, 0)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_relation

        def accept(self, visitor):
            if hasattr(visitor, "visitRelation"):
                return visitor.visitRelation(self)
            else:
                return visitor.visitChildren(self)




    def relation(self):

        localctx = SpecificationGrammarParser.RelationContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_relation)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 60
            self.expr()
            self.state = 63
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if (((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.LEQ) | (1 << SpecificationGrammarParser.EQ) | (1 << SpecificationGrammarParser.GEQ) | (1 << SpecificationGrammarParser.LT) | (1 << SpecificationGrammarParser.GT) | (1 << SpecificationGrammarParser.NEQ))) != 0):
                self.state = 61
                _la = self._input.LA(1)
                if not((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.LEQ) | (1 << SpecificationGrammarParser.EQ) | (1 << SpecificationGrammarParser.GEQ) | (1 << SpecificationGrammarParser.LT) | (1 << SpecificationGrammarParser.GT) | (1 << SpecificationGrammarParser.NEQ))) != 0)):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 62
                self.expr()


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class ExprContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.ExprContext, self).__init__(parent, invokingState)
            self.parser = parser

        def term(self, i=None):
            if i is None:
                return self.getTypedRuleContexts(SpecificationGrammarParser.TermContext)
            else:
                return self.getTypedRuleContext(SpecificationGrammarParser.TermContext,i)


        def PLUS(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.PLUS)
            else:
                return self.getToken(SpecificationGrammarParser.PLUS, i)

        def MINUS(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.MINUS)
            else:
                return self.getToken(SpecificationGrammarParser.MINUS, i)

        def TIMES(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.TIMES)
            else:
                return self.getToken(SpecificationGrammarParser.TIMES, i)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_expr

        def accept(self, visitor):
            if hasattr(visitor, "visitExpr"):
                return visitor.visitExpr(self)
            else:
                return visitor.visitChildren(self)




    def expr(self):

        localctx = SpecificationGrammarParser.ExprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 12, self.RULE_expr)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 65
            self.term()
            self.state = 70
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while (((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.PLUS) | (1 << SpecificationGrammarParser.MINUS) | (1 << SpecificationGrammarParser.TIMES))) != 0):
                self.state = 66
                _la = self._input.LA(1)
                if not((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.PLUS) | (1 << SpecificationGrammarParser.MINUS) | (1 << SpecificationGrammarParser.TIMES))) != 0)):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 67
                self.term()
                self.state = 72
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class TermContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.TermContext, self).__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_term

     
        def copyFrom(self, ctx):
            super(SpecificationGrammarParser.TermContext, self).copyFrom(ctx)



    class TermContextContext(TermContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.TermContext)
            super(SpecificationGrammarParser.TermContextContext, self).__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(SpecificationGrammarParser.ID, 0)

        def accept(self, visitor):
            if hasattr(visitor, "visitTermContext"):
                return visitor.visitTermContext(self)
            else:
                return visitor.visitChildren(self)


    class TermFeatureContext(TermContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.TermContext)
            super(SpecificationGrammarParser.TermFeatureContext, self).__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(SpecificationGrammarParser.ID, 0)

        def accept(self, visitor):
            if hasattr(visitor, "visitTermFeature"):
                return visitor.visitTermFeature(self)
            else:
                return visitor.visitChildren(self)


    class TermIntContext(TermContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.TermContext)
            super(SpecificationGrammarParser.TermIntContext, self).__init__(parser)
            self.copyFrom(ctx)

        def INT(self):
            return self.getToken(SpecificationGrammarParser.INT, 0)

        def accept(self, visitor):
            if hasattr(visitor, "visitTermInt"):
                return visitor.visitTermInt(self)
            else:
                return visitor.visitChildren(self)


    class TermBracketsContext(TermContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.TermContext)
            super(SpecificationGrammarParser.TermBracketsContext, self).__init__(parser)
            self.copyFrom(ctx)

        def b_expr(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.B_exprContext,0)


        def accept(self, visitor):
            if hasattr(visitor, "visitTermBrackets"):
                return visitor.visitTermBrackets(self)
            else:
                return visitor.visitChildren(self)


    class TermAttributeContext(TermContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.TermContext)
            super(SpecificationGrammarParser.TermAttributeContext, self).__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(SpecificationGrammarParser.ID, 0)

        def accept(self, visitor):
            if hasattr(visitor, "visitTermAttribute"):
                return visitor.visitTermAttribute(self)
            else:
                return visitor.visitChildren(self)



    def term(self):

        localctx = SpecificationGrammarParser.TermContext(self, self._ctx, self.state)
        self.enterRule(localctx, 14, self.RULE_term)
        try:
            self.state = 87
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [SpecificationGrammarParser.INT]:
                localctx = SpecificationGrammarParser.TermIntContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 73
                self.match(SpecificationGrammarParser.INT)
                pass
            elif token in [SpecificationGrammarParser.T__6]:
                localctx = SpecificationGrammarParser.TermContextContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 74
                self.match(SpecificationGrammarParser.T__6)
                self.state = 75
                self.match(SpecificationGrammarParser.ID)
                self.state = 76
                self.match(SpecificationGrammarParser.T__2)
                pass
            elif token in [SpecificationGrammarParser.T__7]:
                localctx = SpecificationGrammarParser.TermFeatureContext(self, localctx)
                self.enterOuterAlt(localctx, 3)
                self.state = 77
                self.match(SpecificationGrammarParser.T__7)
                self.state = 78
                self.match(SpecificationGrammarParser.ID)
                self.state = 79
                self.match(SpecificationGrammarParser.T__2)
                pass
            elif token in [SpecificationGrammarParser.T__1]:
                localctx = SpecificationGrammarParser.TermAttributeContext(self, localctx)
                self.enterOuterAlt(localctx, 4)
                self.state = 80
                self.match(SpecificationGrammarParser.T__1)
                self.state = 81
                self.match(SpecificationGrammarParser.ID)
                self.state = 82
                self.match(SpecificationGrammarParser.T__2)
                pass
            elif token in [SpecificationGrammarParser.T__0]:
                localctx = SpecificationGrammarParser.TermBracketsContext(self, localctx)
                self.enterOuterAlt(localctx, 5)
                self.state = 83
                self.match(SpecificationGrammarParser.T__0)
                self.state = 84
                self.b_expr()
                self.state = 85
                self.match(SpecificationGrammarParser.T__3)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class BoolFactContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.BoolFactContext, self).__init__(parent, invokingState)
            self.parser = parser

        def TRUE(self):
            return self.getToken(SpecificationGrammarParser.TRUE, 0)

        def FALSE(self):
            return self.getToken(SpecificationGrammarParser.FALSE, 0)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_boolFact

        def accept(self, visitor):
            if hasattr(visitor, "visitBoolFact"):
                return visitor.visitBoolFact(self)
            else:
                return visitor.visitChildren(self)




    def boolFact(self):

        localctx = SpecificationGrammarParser.BoolFactContext(self, self._ctx, self.state)
        self.enterRule(localctx, 16, self.RULE_boolFact)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 89
            _la = self._input.LA(1)
            if not(_la==SpecificationGrammarParser.TRUE or _la==SpecificationGrammarParser.FALSE):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





