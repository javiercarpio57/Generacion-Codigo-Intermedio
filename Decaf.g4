// antlr4 Decaf.g4; javac Decaf*.java; grun Decaf program -gui fact_struct.decaf
// grun Decaf program -gui fact_struct.decaf
// antlr4 -Dlanguage=Python3 Decaf.g4

// antlr4 Decaf.g4; javac Decaf*.java; antlr4 -Dlanguage=Python3 Decaf.g4

grammar Decaf;

/*
 * Lexer Rules
 */

// Keyword specification

CLASS               : 'class';

PROGRAM             : 'Program';

IF                  : 'if';

ELSE                : 'else';

FOR                 : 'for';

WHILE               : 'while';

RETURN              : 'return';

BREAK               : 'break';

CONTINUE            : 'continue';

BOOLEAN             : 'boolean';

CHAR                : 'char';

INT                 : 'int';

TRUE                : 'True';

FALSE               : 'False';

VOID                : 'void';

STRUCT              : 'struct';

CALLOUT             : 'callout';

// Symbol Specification
SEMICOLON           : ';';

LCURLY              : '{';

RCURLY              : '}';

LSQUARE             : '[';

RSQUARE             : ']';

LROUND              : '(';

RROUND              : ')';

COMMA               : ',';

QUOTES              : '"';

APOSTROPHE          : '\'';

ADD                 : '+';

SUB                 : '-';

MULTIPLY            : '*';

DIVIDE              : '/';

REMINDER            : '%';

AND                 : '&&';

OR                  : '||';

NOT                 : '!';

GREATER_OP          : '>';

LESS_OP             : '<';

GREATER_eq_op       : '>=';

LESS_eq_op          : '<=';

EQUAL_OP            : '=';

ADD_eq_op           : '+=';

SUB_eq_op           : '-=';

EQUALITY_OP         : '==';

UNEQUALITY_OP       : '!=';

POINT               : '.';


// Variable names & literal specification

ID                  : ALPHA ALPHA_NUM*; // for variable name

ALPHA               : [a-zA-Z_];

DECIMAL_LITERAL     : [0-9]+;

DIGIT               : [0-9];

//BOOL_LITERAL        : 'True' | 'False';

STRING_LITERAL      : ('"' ( ALPHA_NUM ) '"') | (APOSTROPHE ( ALPHA_NUM ) APOSTROPHE);

ALPHA_NUM           : ALPHA | DIGIT;

HEX_DIGIT  : '0'[xX]([0-9] | [a-fA-F]);

LINE_COMMENT        : '//' .*? '\n' -> skip; // skip single line comments starting from // and ending with new line

COMMENT             : '/*' .*? '*/' -> skip; // skip mutliple comments

//SPACE               : ' ' -> skip; // ignore spaces

NEWLINE				: ('\r'? '\n' | '\r')+ -> skip;


/*
 * Parser Rules
 */

program		        : CLASS PROGRAM LCURLY (declaration)* RCURLY;

declaration         : struct_declr | vardeclr | method_declr | field_declr ;

vardeclr            : var_type field_var SEMICOLON;

field_declr         : var_type field_var (COMMA field_var)* SEMICOLON;

array_id            : ID LSQUARE (int_literal | var_id | expr) RSQUARE (POINT location)?;

field_var           : var_id | array_id;

var_id              : ID (POINT location)?;

struct_declr        : STRUCT ID LCURLY (vardeclr)* RCURLY SEMICOLON;

method_declr        : return_type method_name LROUND (((var_type var_id) | VOID) (COMMA var_type var_id)*)? RROUND block;

return_type         : (var_type | VOID);

block               : LCURLY (vardeclr)* statement* RCURLY;

statement           : location assign_op expr SEMICOLON? #statement_assign
                    | method_call #statement_methodcall
                    | IF LROUND expr RROUND block (ELSE block)? #statement_if
                    | WHILE LROUND expr RROUND block #statement_while
                    | RETURN expr SEMICOLON #statement_return
                    | FOR var_id (EQUAL_OP int_literal)? COMMA ((var_id (EQUAL_OP int_literal)?) | int_literal) block #statement_for
                    | BREAK SEMICOLON #statement_break
                    ; 

method_call         : method_name LROUND (expr (COMMA expr)*)? RROUND (SEMICOLON)?;

expr                : literal
                    | location
                    | SUB expr
                    | NOT expr
                    | expr (MULTIPLY | DIVIDE | REMINDER) expr
                    | expr (ADD | SUB) expr
                    | expr (AND) expr
                    | expr (OR) expr
                    | expr ( rel_op | eq_op ) expr
                    | method_call
                    | LROUND expr RROUND
                    ;


location            : var_id | array_id;

int_literal         : DECIMAL_LITERAL;

string_literal      : STRING_LITERAL;

bool_literal        : 'True' | 'False';

rel_op              : GREATER_OP | LESS_OP | LESS_eq_op | GREATER_eq_op;

eq_op               : EQUALITY_OP | UNEQUALITY_OP;

cond_op             : AND | OR;

literal             : int_literal | string_literal | bool_literal;

arith_op            : MULTIPLY | DIVIDE | REMINDER | ADD | SUB ;

var_type            : INT | CHAR | BOOLEAN | STRUCT ID | struct_declr ;

assign_op           : EQUAL_OP
                    | ADD_eq_op
                    | SUB_eq_op;

method_name         : ID;

// recognize the whitespace at the end to prevent string concatenation due to elemination of all sapces
WHITESPACE			: [ \t\r\n] -> skip ;