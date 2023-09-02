import ply.lex as lex

# List of token names.   This is always required
tokens = (
   'ID',
   'NUMBER',
   'PLUS',
   'MINUS',
   'TIMES',
   # 'DIVIDE',
   'LPAREN',
   'RPAREN',
   'LBRACE',
   'RBRACE',
   'GT',
   'LT',
   'GE',
   'LE',
   'NE',
   'SEMI',
   'EQ',
   'ASSIGN',
   'INCRE',
   'PE',
   'DECRE',
   'ME',
   'MOD',
   'NOT',
   'COMMA',
)

# Regular expression rules for simple tokens
t_PLUS    = r'\+'
t_MINUS   = r'-'
t_TIMES   = r'\*'
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_LBRACE  = r'\{'
t_RBRACE  = r'\}'
t_IF = r'IF'
t_GT = '>'
t_GE = '>='
t_LT = '<'
t_LE = '<='
t_NE = r'!='
t_EQ = r'=='
t_SEMI = r';'
t_ASSIGN = r'='
t_INCRE = r'\+\+'
t_PE = r'\+='
t_DECRE = r'--'
t_ME = r'-='
t_MOD = r'%'
t_NOT = r'!'
t_AND = r'AND'
t_OR = r'OR'
t_COMMA = r','

reserved = {
   'if' : 'IF',
   'else' : 'ELSE',
   'true': 'TRUE',
   'And': 'AND',
   'Or': 'OR',
   'True': 'TRUE'
}

tokens = tuple(list(tokens) + list(set(reserved.values())))

def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.type = reserved.get(t.value,'ID')    # Check for reserved words
    return t

# A regular expression rule with some action code
def t_NUMBER(t):
    r'-?\d+'
    t.value = int(t.value)
    t.type = 'NUMBER'
    return t

# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t'

# Error handling rule
def t_error(t):
    print("Line %d: Illegal character '%s'" % (t.lexer.lineno, t.value[0]))
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex()