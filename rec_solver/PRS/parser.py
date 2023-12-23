import ply.yacc as yacc
import sympy as sp

from .lexer import tokens, lexer
from .condition import PolyCondition, And, ModCondition, TrueCondition, Or, NondetCondition

def internal_name(name):
    if name.startswith(PREFIX):
        return name
    return PREFIX + name

def outside_name(name):
    if name.startswith(PREFIX):
        return name[len(PREFIX):]
    return name

precedence = (
     ('left', 'PLUS', 'MINUS'),
     ('left', 'TIMES'),
 )

PREFIX = ''
INDEX = sp.Symbol(PREFIX + 'n', integer=True)

variables = []

def p_program(p):
    '''program : initializations if'''
    cond, maps = p[2]
    symbols_in_trans = set()
    for c in cond:
        symbols_in_trans = symbols_in_trans.union(c.free_symbols)
    for m in maps:
        for v in m.values():
            symbols_in_trans = symbols_in_trans.union(v.free_symbols)
    symbols_in_trans = symbols_in_trans - {sp.Symbol('constant')}
    for s in symbols_in_trans:
        if str(s) not in variables:
            variables.append(str(s))
    variables.append('constant')
    x0 = sp.zeros(len(variables), 1)
    for i, var in enumerate(variables[:-1]):
        x0[i] = sp.Symbol(var)
    for i, var in enumerate(variables[:len(p[1])]):
        x0[i] = p[1][var]
    x0[-1] = 1
    # p[0] = (cond, x0, A, [sp.Symbol(var) for var in variables], INDEX)
    p[0] = (cond, x0, maps, [sp.Symbol(var) for var in variables], INDEX)

def p_initializations1(p):
    '''initializations : initialization initializations'''
    # full = p[1]
    # full.update(p[2])
    p[0] = p[1] | p[2]

def p_initializations2(p):
    '''initializations : '''
    p[0] = {}
    # variables.append(internal_name('constant'))
    # p[0] = {internal_name('constant'): sp.Integer(1)}

# def p_initialization_1(p):
#     '''initialization : ID ASSIGN const SEMI'''
#     variables.append(internal_name(p[1]))
#     p[0] = {internal_name(p[1]): p[3]}

def p_initialization_1(p):
    '''initialization : ID ASSIGN expression SEMI'''
    variables.append(internal_name(p[1]))
    p[0] = {internal_name(p[1]): p[3]}

# def p_const(p):
#     '''const : NUMBER
#              | ID'''
#     p[0] = p[1]

# def p_statements(p):
#     '''statements : statement statements
#                   |'''
#     pass

# def p_statement(p):
#     '''statement : if
#                  | assignment
#                  | LBRACE statements RBRACE'''
#     pass

# def p_assignments(p):
#     '''assignments : assignment assignments
#                    | LBRACE assignments RBRACE
#                    | '''
#     if len(p) == 3:
#         p[0] = p[2] + p[1]
#     elif len(p) == 4:
#         p[0] = p[2]
#     else:
#         p[0] = [(internal_name('constant'), sp.Matrix([[0]*(len(variables)-1) + [1]]))]

def p_assignments1(p):
    '''assignments : assignment assignments'''
    p[0] = p[2] | p[1]

def p_assignments2(p):
    '''assignments : LBRACE assignments RBRACE'''
    p[0] = p[2]

def p_assignments3(p):
    '''assignments : '''
    p[0] = {internal_name('constant'): sp.Symbol('constant')}

def p_assignment1(p):
    '''assignment : ID ASSIGN expression SEMI'''
    exp = sp.expand(p[3])
    coef_vec = sp.zeros(1, len(variables))

    # for i, var in enumerate(variables):
    #     coeff = exp.coeff(var)
    #     coef_vec[i] = coeff
    #     exp -= coeff*sp.Symbol(var)
    # coef_vec[-1] = exp
    p[0] = {internal_name(p[1]): exp}
    # p[0] = [(internal_name(p[1]), coef_vec)]

def p_assignment2(p):
    '''assignment : ID INCRE SEMI'''
    # i = variables.index(internal_name(p[1]))
    # coef_vec = sp.zeros(1, len(variables))
    # coef_vec[i] = 1
    # coef_vec[-1] = 1
    p[0] = {internal_name(p[1]): p[1] + 1}

def p_assignment3(p):
    '''assignment : ID DECRE SEMI'''
    # i = variables.index(internal_name(p[1]))
    # coef_vec = sp.zeros(1, len(variables))
    # coef_vec[i] = 1
    # coef_vec[-1] = -1
    p[0] = {internal_name(p[1]): p[1] - 1}

def p_assignment4(p):
    '''assignment : ID PE NUMBER SEMI'''
    # i = variables.index(internal_name(p[1]))
    # coef_vec = sp.zeros(1, len(variables))
    # coef_vec[i] = 1
    # coef_vec[-1] = p[3]
    p[0] = {internal_name(p[1]): p[1] + p[3]}

def p_assignment5(p):
    '''assignment : ID ME NUMBER SEMI'''
    # i = variables.index(internal_name(p[1]))
    # coef_vec = sp.zeros(1, len(variables))
    # coef_vec[i] = 1
    # coef_vec[-1] = -p[3]
    p[0] = {internal_name(p[1]): p[1] - p[3]}


# def p_assignment(p):
#     '''assignment : ID ASSIGN expression SEMI
#                   | ID INCRE SEMI
#                   | ID PE NUMBER SEMI
#                   | ID ME NUMBER SEMI
#                   | ID DECRE SEMI'''
#     if len(p) == 5 and p[2] == '=':
#         exp = sp.expand(p[3])
#         coef_vec = sp.zeros(1, len(variables))
# 
#         for i, var in enumerate(variables):
#             if sp.simplify(sp.diff(exp, var, 2)) != 0:
#                 raise TypeError('%s is not linear' % p[3])
#             coeff = exp.coeff(var)
#             coef_vec[i] = coeff
#             exp -= coeff*sp.Symbol(var)
#         coef_vec[-1] = exp
#         p[0] = [(internal_name(p[1]), coef_vec)]
# 
#     elif len(p) == 4:
#         i = variables.index(internal_name(p[1]))
#         coef_vec = sp.zeros(1, len(variables))
#         coef_vec[i] = 1
#         if p[2] == '++':
#             coef_vec[-1] = 1
#         else:
#             coef_vec[-1] = -1
#         p[0] = [(internal_name(p[1]), coef_vec)]
#     elif len(p) == 5:
#         i = variables.index(internal_name(p[1]))
#         coef_vec = sp.zeros(1, len(variables))
#         coef_vec[i] = 1
#         if p[2] == '+=':
#             coef_vec[-1] = p[3]
#         else:
#             coef_vec[-1] = -p[3]
#         p[0] = [(internal_name(p[1]), coef_vec)]


                 # expression MOD NUMBER EQ NUMBER
def p_condition1(p):
    '''condition : expression cmpop expression'''
    if _contains_mod(p[1]):
        lhs, rhs = p[1].args
        p[0] = ModCondition(lhs - p[3], rhs)
    elif _contains_mod(p[3]):
        lhs, rhs = p[3].args
        p[0] = ModCondition(lhs - p[1], rhs)
    elif p[2] == '>=':
        p[0] = PolyCondition(p[1]-p[3])
    elif p[2] == '>':
        p[0] = PolyCondition(p[1]-p[3], strict=True)
    elif p[2] == '<':
        p[0] = PolyCondition(p[3]-p[1], strict=True)
    elif p[2] == '<=':
        p[0] = PolyCondition(p[3]-p[1])
    elif p[2] == '==':
        p[0] = And(PolyCondition(p[3]-p[1]), PolyCondition(p[1]-p[3]))
    # elif len(p) == 6:
    #     p[0] = ModCondition(p[1] - p[5], p[3])
    # elif p[2] == '!=':
    #     p[0] = sp.Ne(p[1], p[3])

def p_condition2(p):
    '''condition : NOT LPAREN condition RPAREN'''
    p[0] = p[3].neg()


def p_condition3(p):
    '''condition : AND LPAREN condition_list RPAREN'''
    res = And(p[3][0], p[3][1])
    for c in p[3][2:]:
        res = And(res, c)
    p[0] = res

def p_condition_4(p):
    '''condition : TRUE'''
    p[0] = TrueCondition(True)

def p_condition_5(p):
    '''condition : OR LPAREN condition_list RPAREN'''
    res = Or(p[3][0], p[3][1])
    for c in p[3][2:]:
        res = And(res, c)
    p[0] = res

def p_condition_6(p):
    '''condition : TIMES'''
    p[0] = NondetCondition()

# def p_condition_4(p):
#     '''condition : NUMBER EQ expression MOD NUMBER'''
#     p[0] = ModCondition(p[3] - p[1], p[5])

def p_condition_list_1(p):
    '''condition_list : condition COMMA condition_list'''
    p[0] = [p[1]] + p[3]

def p_condition_list_2(p):
    '''condition_list : condition'''
    p[0] = [p[1]]

def p_cmpop(p):
    '''cmpop : GT
             | GE
             | LT
             | LE
             | EQ
             | NE'''
    p[0] = p[1]

# def p_if(p):
#     '''if : IF LPAREN condition RPAREN assignments
#           | IF LPAREN condition RPAREN assignments ELSE assignments
#           | IF LPAREN condition RPAREN assignments ELSE if'''
#     if_statement = sp.eye(len(variables))
#     for var, matrix in p[5]:
#         i = variables.index(var)
#         if_statement[i, :] = matrix
#     if len(p) == 6:
#         else_statement = sp.eye(len(variables))
#         p[0] = ([p[3]], [if_statement, else_statement])
#     elif isinstance(p[7], tuple):
#         p[0] = ([p[3]] + p[7][0], [if_statement] + p[7][1])
#     else:
#         else_statement = sp.eye(len(variables))
#         for var, matrix in p[7]:
#             i = variables.index(var)
#             else_statement[i, :] = matrix
#         p[0] = ([p[3]], [if_statement, else_statement])

def p_if_1(p):
    '''if : IF LPAREN condition RPAREN assignments'''
    true_transition = p[5]
    false_transition = {v: sp.Symbol(v) for v in variables + ['constant']}
    if isinstance(p[3], TrueCondition):
        p[0] = ([p[3]], [true_transition])
    else:
        p[0] = ([p[3]], [true_transition, false_transition])

def p_if_2(p):
    '''if : IF LPAREN condition RPAREN assignments ELSE assignments'''
    true_transition = p[5]
    false_transition = p[7]
    p[0] = ([p[3]], [true_transition, false_transition])

def p_if_3(p):
    '''if : IF LPAREN condition RPAREN assignments ELSE if'''
    true_transition = p[5]
    p[0] = ([[p[3]]] + p[7][0], [true_transition] + p[7][1])



def p_expression(p):
    '''expression : expression PLUS factor
                  | expression MINUS factor
                  | factor'''
    if len(p) == 2:
        p[0] = p[1]
        # p[0] = sp.Symbol(internal_name(p[1])) if isinstance(p[1], str) else p[1]
    elif p[2] == '+':
        p[0] = p[1] + p[3]
    elif p[2] == '-':
        p[0] = p[1] - p[3]

# def p_factor(p):
#     '''factor : factor TIMES unary_expression
#               | factor MOD unary_expression
#               | unary_expression'''
#     if len(p) == 2:
#         p[0] = p[1]
#     elif p[2] == '*':
#         p[0] = p[1] * p[3]
#     else:
#         p[0] = p[1] % p[3]

def p_factor1(p):
    '''factor : factor TIMES unary_expression'''
    p[0] = p[1]*p[3]

def p_factor2(p):
    '''factor : factor MOD unary_expression'''
    p[0] = p[1] % p[3]

def p_factor3(p):
    '''factor : unary_expression'''
    p[0] = p[1]

def p_factor4(p):
    '''factor : factor DIV unary_expression'''
    p[0] = p[1] / p[3]


def p_unary_expression_1(p):
    '''unary_expression : PLUS symbol_number
                        | MINUS symbol_number
                        | symbol_number
                        | LPAREN expression RPAREN'''
    if len(p) == 2:
        p[0] = p[1]
    elif len(p) == 4:
        p[0] = p[2]
    elif p[1] == '+':
        p[0] = p[2]
    elif p[1] == '-':
        p[0] = -p[2]
    else:
        raise Exception('Unary operations except "+" and "-" are not supported yet')

# def p_unary_expression_2(p):
#     '''unary_expression : PLUS ID
#                         | MINUS ID'''
#     if p[1] == '+':
#         p[0] = sp.Symbol(p[2])
#     elif p[1] == '-':
#         p[0] = -sp.Symbol(p[2])
#     else:
#         raise Exception('Unary operations except "+" and "-" are not supported yet')

def p_symbol_number(p):
    '''symbol_number : NUMBER
                     | ID'''
    if isinstance(p[1], int):
        p[0] = sp.Integer(p[1])
    else:
        p[0] = sp.Symbol(p[1])

# Error rule for syntax errors
def p_error(p):
    print("Syntax error in input!")
    print(p)


################################################### helper functions ###########################################
def _contains_mod(p):
    return 'Mod' in str(p)
# Build the parser

parser = yacc.yacc()
def parse(recurrence):
    global variables
    variables = []
    return parser.parse(recurrence, lexer=lexer)

if __name__ == '__main__':
    data = '''x = 10; if (x > 0) { x = x + 1; } else if (x + 5 < 0) { x = x + 2; }'''
    result = parser.parse(data)
    print(result)
# while True:
#    try:
#        s = input('calc > ')
#    except EOFError:
#        break
#    if not s: continue
#    result = parser.parse(s)
#    print(result)