grammar SpecificationGrammar;

// To generate files run antlr4 -Dlanguage=Python2 -visitor -no-listener

preference:
  constraint                          #constraintPreference |
  (MIN | MAX) '(' attribute ')' EOF   #minMaxPreference;
 
 
constraint : b_expr EOF;

b_expr : b_term (bool_binary_op b_term )* ;

b_term : (unaryOp)? b_factor ;

b_factor : boolFact | relation ; 

relation : expr (comparison_op expr)? ;

expr : term (arith_binary_op term)* ;

term :
  INT                       |
  context                   |
  feature                   |
  attribute                 | 
  arith_unary_op expr       |  
  '(' b_expr ')'            ;

context : 'context[' INT ']';

feature : 'feature[' INT ']';

attribute : 'attribute[' INT '][' INT ']';

comparison_op : LEQ | EQ | GEQ | LT | GT | NEQ ;
boolFact : TRUE | FALSE;
bool_binary_op : AND | OR | IMPL | IFF | XOR;
arith_binary_op : PLUS | MINUS | TIMES ;
arith_unary_op : ABS ;
unaryOp : NOT;


AND : 'and';
OR : 'or';
XOR : 'xor';
NOT : 'not';
TRUE : 'true';
FALSE : 'false';
IMPL: 'impl';
IFF: 'iff';
MIN: 'min';
MAX: 'max';
ABS: 'abs';

LEQ : '<=';
EQ : '=';
GEQ : '>=';
LT : '<';
GT : '>';
NEQ : '!=';

PLUS : '+';
MINUS : '-';
TIMES : '*';
      
ID : [a-zA-Z_][a-zA-Z0-9_]* ;    // match letters, numbers, underscore
INT : [-]?[0-9]+ ;
WS : [ \t\r\n]+ -> skip ; // skip spaces, tabs, newlines
