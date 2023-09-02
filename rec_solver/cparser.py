# -----------------------------------------------------------------------------
# cparse.py
#
# Simple parser for ANSI C.  Based on the grammar in K&R, 2nd Ed.
# -----------------------------------------------------------------------------

import sys
import clexer
import ply.yacc as yacc
import sympy as sp
import utils
from PRS.prs_solver import solve_str
import os
import shutil
import csv
import time
# from condition import PolyCondition, Condition
from sympy.logic.boolalg import And, Or, Not
from sympy import Ne, Rational
from PRS.mathematica_manipulation import clean
def and_str(self):
    return 'And(%s)' % ', '.join(str(arg) for arg in self.args)

def or_str(self):
    return 'Or(%s)' % ', '.join(str(arg) for arg in self.args)

def not_str(self):
    return 'Not(%s)' % self.args[0]

def ne_str(self):
    return 'Not(%s == %s)' % (self.lhs, self.rhs)


And.__str__ = and_str
Or.__str__ = or_str
Not.__str__ = not_str
Ne.__str__ = ne_str
# Get the token map
tokens = clexer.tokens

# translation-unit:

init_num = 0
tmp_num = 0
variables = {}
temp_variables = set()
temp_variables_type = {}
z3query = ''
tested_filename = ''
exception_path = 'exception'
standard_path = 'loop'
queries_path = 'queries'
extracted_recurrence_path = 'extracted_recurrence'
closed_form_solution = 'closed_form_solution'
headers = ['filename', 'time', 'average time', 'min time', 'max time']
stats = []
experiment = False
N_index = 0
assertions = []
assertion = ''

def p_translation_unit_1(p):
    'translation_unit : external_declaration'
    pass


def p_translation_unit_2(p):
    'translation_unit : translation_unit external_declaration'
    pass

# external-declaration:


def p_external_declaration_1(p):
    'external_declaration : function_definition'
    pass


def p_external_declaration_2(p):
    'external_declaration : declaration'
    pass

# function-definition:


def p_function_definition_1(p):
    'function_definition : declaration_specifiers declarator declaration_list compound_statement'
    pass


def p_function_definition_2(p):
    'function_definition : declarator declaration_list compound_statement'
    pass


def p_function_definition_3(p):
    'function_definition : declarator compound_statement'
    pass


def p_function_definition_4(p):
    'function_definition : declaration_specifiers declarator compound_statement'
    global variables
    global N_index
    global assertion
    z3functions = set()
    statements = p[3]
    values = {}
    if p[2][0].name == 'main':
        has_encountered = False
        z3 = ''
        for statement in statements:
            if has_encountered:
                break
            if utils.is_assignment_list(statement):
                for assign in statement:
                    lhs = utils.get_assignment_lhs(assign)
                    rhs = utils.get_assignment_rhs(assign)
                    rhs = rhs.subs(values, simultaneous=True)
                    values.update({lhs: rhs})
                    variables.setdefault(lhs, 0)
                    variables[lhs] += 1
                    mapping = {k: sp.Symbol('%s%d' % (k, variables[k])) for k in variables}
                    z3 += 's.add(%s == %s)\n' % (lhs.subs(mapping, simultaneous=True), rhs.subs(mapping))
            elif utils.is_assignment(statement):
                assign = statement
                # for assign in statement:
                lhs = utils.get_assignment_lhs(assign)
                rhs = utils.get_assignment_rhs(assign)
                rhs = rhs.subs(values, simultaneous=True)
                values.update({lhs: rhs})
                variables.setdefault(lhs, 0)
                variables[lhs] += 1
                mapping = {k: sp.Symbol('%s%d' % (k, variables[k])) for k in variables}
                z3 += 's.add(%s == %s)\n' % (lhs.subs(mapping, simultaneous=True), rhs.subs(mapping))
            elif utils.is_selection(statement):
                if utils.is_return(statement[1][0]):
                    cond = utils.get_selection_cond(statement)
                    cond = cond.subs(values, simultaneous=True)
                    z3 += 's.add(%s)\n' % (sp.Not(cond))
                elif utils.is_assertion(statement[1][0]):
                    cond = utils.get_selection_cond(statement)
                    cond = cond.subs(values, simultaneous=True)
                    _, args = utils.function_name_args(statement[1][0])
                    mapping = {k: sp.Symbol('%s%d' % (k, variables[k])) for k in variables}
                    conclusion = utils.relation2str(args[0].subs(mapping))
                    # z3 += 's.add(Not(Or(Not(%s), And(%s, %s))))\n' % (cond, cond, conclusion)
                    assertion = 'Or(Not(%s), And(%s, %s))' % (cond, cond, conclusion)
                    has_encountered = True
                    # z3 += 's.add(Implies(%s, Not(%s)))\n' % (cond.subs(values, simultaneous=True), utils.relation2str(args[0].subs(mapping)))
            elif utils.is_function_call(statement):
                name, args = utils.function_name_args(statement)
                mapping = {k: sp.Symbol('%s%d' % (k, variables[k])) for k in variables}
                if name.name == utils.assert_call:
                    z3 += '#'*10 + ' assert ' + '#'*10 + '\n'
                    # z3 += 's.add(Not(%s))\n' % utils.relation2str(args[0].subs(mapping))
                    assertion = '%s' % utils.relation2str(args[0].subs(mapping))
                    has_encountered = True
                    z3 += '#'*10 + '########' + '#'*10 + '\n'
            elif utils.is_iteration(statement):
                assertion = statement[1]
                PRS_recurrence = utils.to_PRS(values, (statement[2], statement[3]))
                if experiment:
                    with open(os.path.join(extracted_recurrence_path, os.path.basename(tested_filename)), 'a') as fp:
                        fp.write(PRS_recurrence)
                # print(PRS_recurrence)
                start_time = time.time()
                closed_form, var_order, index, t = solve_str(PRS_recurrence)
                total_time = time.time() - start_time
                stats.append([tested_filename, total_time, '', '', ''])
                if experiment:
                    with open(os.path.join(closed_form_solution, os.path.basename(tested_filename)), 'a') as fp:
                        fp.write(str(closed_form))
                # print(closed_form)
                bodies, conds = statement[2], statement[3]
                involved_variables = bodies[0].keys()
                variables = {var: variables[var] if var not in involved_variables else variables[var]+1 for var in variables}
                old_mapping = {k: sp.Symbol('%s%d(n)' % (k, variables[k])) for k in variables}
                for var in involved_variables:
                    z3 += 's.add(%s%d(0) == %s%d)\n' % (var, variables[var], var, variables[var]-1)
                    new_mapping = {k: '%s%d(n+1)' % (k, variables[k]) for k in variables}
                    recurrence = ('ForAll(n, Implies(n >= 0, %s == If(%s, %s, %s)))' % (var.subs(new_mapping, simultaneous=True), '%s', '%s', '%s'))
                    z3functions.add('%s%d' % (var, variables[var]))
                    for i, (body, cond) in enumerate(zip(bodies, conds)):
                        c = cond.subs(old_mapping, simultaneous=True)
                        if isinstance(c, sp.Eq):
                            c = '%s == %s' % (c.lhs, c.rhs)
                        else:
                            c = '%s' % c
                        if i < len(conds) - 1:
                            recurrence = (recurrence % (c, body[var].subs(old_mapping, simultaneous=True), 'If(%s, %s, %s)'))
                        else:
                            recurrence = (recurrence % (c, body[var].subs(old_mapping, simultaneous=True), '%s'))
                    recurrence = recurrence % bodies[-1][var].subs(old_mapping, simultaneous=True)
                    z3 += 's.add(%s)\n' % recurrence
                    # closed_form_index = var_order.index(var.name)
                    coef, closed_form_str = utils.closed_form2z3(closed_form, var_order, var, index)
                    z3 += '#'*10 + ' closed form ' + '#'*10 + '\n'
                    if coef != 1:
                        z3 += 's.add(ForAll(n, Implies(n >= 0, %d*%s%d(n) == %s)))\n' % (coef, var, variables[var], closed_form_str)
                    else:
                        z3 += 's.add(ForAll(n, Implies(n >= 0, %s%d(n) == %s)))\n' % (var, variables[var], closed_form_str)
                    z3 += '#'*10 + '#############' + '#'*10 + '\n'
                    variables[var] += 1
                    N = 'N%d' % N_index
                    z3 += 's.add(%s%d == %s%d(%s))\n' % (var, variables[var], var, variables[var]-1, N)
                    values.update({var: sp.Symbol('%s%d' % (var, variables[var]))})
                cond_mapping = {k: sp.Symbol(('%s%d(n)' if k in involved_variables else '%s%d') % (k, variables[k]-1 if k in involved_variables else variables[k])) for k in variables}
                z3 += 's.add(ForAll(n, Implies(And(0 <= n, n < %s), %s)))\n' % (N, statement[4].subs(cond_mapping))
                cond_mapping = {k: sp.Symbol(('%%s%%d(%s)' % N if k in involved_variables else '%s%d') % (k, variables[k]-1 if k in involved_variables else variables[k])) for k in variables}
                if statement[4].subs(cond_mapping) != True:
                    z3 += 's.add(Not(%s))\n' % statement[4].subs(cond_mapping)
                N_index += 1
                if assertion is not None:
                    z3 += '#'*10 + ' assertion in loop ' + '#'*10 + '\n'
                    if assertion[1]:
                        assert_mapping = {k: sp.Symbol(('%s%d(n+1)' if k in involved_variables else '%s%d') % (k, variables[k]-1 if k in involved_variables else variables[k])) for k in variables}
                    else:
                        assert_mapping = {k: sp.Symbol(('%s%d(n)' if k in involved_variables else '%s%d') % (k, variables[k]-1 if k in involved_variables else variables[k])) for k in variables}
                    # z3 += 's.add(Not(ForAll(n, Implies(n >= 0, %s))))\n' % assertion.subs(assert_mapping)
                    assertion = 'ForAll(n, Implies(And(0 <= n, n < %s), %s))' % (N, assertion[0].subs(assert_mapping))
                    has_encountered = True
        z3header = 'from z3 import *\n'
        z3header += 'from aux_z3 import *\n'
        z3header += 's = set()\n'
        z3header += 'n = Int("n")\n'
        for n in range(N_index):
            z3header += 'N{0} = Int("N{0}")\n'.format(n)
            z3header += 's.add(N{0} >= 0)\n'.format(n)
        z3header += 'solver = Solver()\n'
        z3header += 'solver.set("timeout", 2000)\n'
        for var, cnt in variables.items():
            for i in range(1, cnt+1):
                symbol = sp.Symbol('%s%d' % (var, i))
                if symbol.name in z3functions:
                    z3header += '%s = Function("%s", IntSort(), IntSort())\n' % (symbol, symbol)
                else:
                    z3header += '%s = Int("%s")\n' % (symbol, symbol)
        for var in temp_variables:
            z3header += '%s = Int("%s")\n' % (var.name, var.name)
            if temp_variables_type[var] == 'uint':
                z3header += 's.add(%s >= 0)\n' % var
        z3 = z3header + z3
        global z3query
        z3query = z3


# declaration:


def p_declaration_1(p):
    'declaration : declaration_specifiers init_declarator_list SEMI'
    p[0] = p[2]


def p_declaration_2(p):
    'declaration : declaration_specifiers SEMI'
    pass

# declaration-list:


def p_declaration_list_1(p):
    'declaration_list : declaration'
    p[0] = [p[1]]


def p_declaration_list_2(p):
    'declaration_list : declaration_list declaration '
    p[0] = p[1] + [p[2]]

# declaration-specifiers


def p_declaration_specifiers_1(p):
    'declaration_specifiers : storage_class_specifier declaration_specifiers'
    pass


def p_declaration_specifiers_2(p):
    'declaration_specifiers : type_specifier declaration_specifiers'
    pass


def p_declaration_specifiers_3(p):
    'declaration_specifiers : type_qualifier declaration_specifiers'
    pass


def p_declaration_specifiers_4(p):
    'declaration_specifiers : storage_class_specifier'
    pass


def p_declaration_specifiers_5(p):
    'declaration_specifiers : type_specifier'
    pass


def p_declaration_specifiers_6(p):
    'declaration_specifiers : type_qualifier'
    pass

# storage-class-specifier


def p_storage_class_specifier(p):
    '''storage_class_specifier : AUTO
                               | REGISTER
                               | STATIC
                               | EXTERN
                               | TYPEDEF
                               '''
    pass

# type-specifier:


def p_type_specifier(p):
    '''type_specifier : VOID
                      | CHAR
                      | SHORT
                      | INT
                      | LONG
                      | FLOAT
                      | DOUBLE
                      | SIGNED
                      | UNSIGNED
                      | struct_or_union_specifier
                      | enum_specifier
                      | TYPEID
                      | BOOL
                      '''
    pass

# type-qualifier:


def p_type_qualifier(p):
    '''type_qualifier : CONST
                      | VOLATILE'''
    pass

# struct-or-union-specifier


def p_struct_or_union_specifier_1(p):
    'struct_or_union_specifier : struct_or_union ID LBRACE struct_declaration_list RBRACE'
    pass


def p_struct_or_union_specifier_2(p):
    'struct_or_union_specifier : struct_or_union LBRACE struct_declaration_list RBRACE'
    pass


def p_struct_or_union_specifier_3(p):
    'struct_or_union_specifier : struct_or_union ID'
    pass

# struct-or-union:


def p_struct_or_union(p):
    '''struct_or_union : STRUCT
                       | UNION
                       '''
    pass

# struct-declaration-list:


def p_struct_declaration_list_1(p):
    'struct_declaration_list : struct_declaration'
    pass


def p_struct_declaration_list_2(p):
    'struct_declaration_list : struct_declaration_list struct_declaration'
    pass

# init-declarator-list:


def p_init_declarator_list_1(p):
    'init_declarator_list : init_declarator'
    p[0] = [p[1]]


def p_init_declarator_list_2(p):
    'init_declarator_list : init_declarator_list COMMA init_declarator'
    p[0] = p[1] + [p[3]]

# init-declarator


def p_init_declarator_1(p):
    'init_declarator : declarator'
    global tmp_num
    if isinstance(p[1], tuple):
        p[0] = None
    elif p[1] is not None:
        symbol = sp.Symbol('tmp%d' % tmp_num)
        p[0] = utils.create_assignment(p[1], symbol)
        # p[0] = ('assip[1], sp.Symbol('%s%d' % (p[1].name, init_num)))
        temp_variables.add(symbol)
        temp_variables_type[symbol] = 'int'
        tmp_num += 1


def p_init_declarator_2(p):
    'init_declarator : declarator EQUALS initializer'
    if isinstance(p[3], tuple) and p[3][0].name.startswith('__VERIFIER_nondet_'):
        variables.setdefault(p[1], 0)
        variables[p[1]] += 1
        temp = sp.Symbol('tmp%d' % tmp_num)
        temp_variables.add(temp)
        p[0] = utils.create_assignment(p[1], temp)
        if p[3][0].name.endswith('uint'):
            temp_variables_type[temp] = 'uint'
        else:
            temp_variables_type[temp] = 'int'
        tmp_num += 1
    else:
        p[0] = utils.create_assignment(p[1], p[3])
    # p[0] = {p[1]: p[3]}

# struct-declaration:


def p_struct_declaration(p):
    'struct_declaration : specifier_qualifier_list struct_declarator_list SEMI'
    pass

# specifier-qualifier-list:


def p_specifier_qualifier_list_1(p):
    'specifier_qualifier_list : type_specifier specifier_qualifier_list'
    pass


def p_specifier_qualifier_list_2(p):
    'specifier_qualifier_list : type_specifier'
    pass


def p_specifier_qualifier_list_3(p):
    'specifier_qualifier_list : type_qualifier specifier_qualifier_list'
    pass


def p_specifier_qualifier_list_4(p):
    'specifier_qualifier_list : type_qualifier'
    pass

# struct-declarator-list:


def p_struct_declarator_list_1(p):
    'struct_declarator_list : struct_declarator'
    pass


def p_struct_declarator_list_2(p):
    'struct_declarator_list : struct_declarator_list COMMA struct_declarator'
    pass

# struct-declarator:


def p_struct_declarator_1(p):
    'struct_declarator : declarator'
    pass


def p_struct_declarator_2(p):
    'struct_declarator : declarator COLON constant_expression'
    pass


def p_struct_declarator_3(p):
    'struct_declarator : COLON constant_expression'
    pass

# enum-specifier:


def p_enum_specifier_1(p):
    'enum_specifier : ENUM ID LBRACE enumerator_list RBRACE'
    pass


def p_enum_specifier_2(p):
    'enum_specifier : ENUM LBRACE enumerator_list RBRACE'
    pass


def p_enum_specifier_3(p):
    'enum_specifier : ENUM ID'
    pass

# enumerator_list:


def p_enumerator_list_1(p):
    'enumerator_list : enumerator'
    pass


def p_enumerator_list_2(p):
    'enumerator_list : enumerator_list COMMA enumerator'
    pass

# enumerator:


def p_enumerator_1(p):
    'enumerator : ID'
    pass


def p_enumerator_2(p):
    'enumerator : ID EQUALS constant_expression'
    pass

# declarator:


def p_declarator_1(p):
    'declarator : pointer direct_declarator'
    pass


def p_declarator_2(p):
    'declarator : direct_declarator'
    p[0] = p[1]

# direct-declarator:


def p_direct_declarator_1(p):
    'direct_declarator : ID'
    p[0] = sp.Symbol(p[1])


def p_direct_declarator_2(p):
    'direct_declarator : LPAREN declarator RPAREN'
    pass


def p_direct_declarator_3(p):
    'direct_declarator : direct_declarator LBRACKET constant_expression_opt RBRACKET'
    pass


def p_direct_declarator_4(p):
    'direct_declarator : direct_declarator LPAREN parameter_type_list RPAREN attributes'
    p[0] = (p[1], *p[3])


def p_direct_declarator_5(p):
    'direct_declarator : direct_declarator LPAREN identifier_list RPAREN '
    pass


def p_direct_declarator_6(p):
    'direct_declarator : direct_declarator LPAREN RPAREN '
    p[0] = (p[1], None)

# def p_direct_declarator_7(p):
#     'direct_declarator : direct_declarator LPAREN parameter_type_list RPAREN attributes'
#     p[0] = (p[1], *p[3])

# attributes
def p_attributes(p):
    '''attributes : attribute attributes
                  | '''
    pass

def p_attribute(p):
    '''attribute : ID attribute_list'''
    pass

def p_attribute_list(p):
    '''attribute_list : LPAREN attribute_list RPAREN
                      | identifier_list'''
    pass

# pointer:


def p_pointer_1(p):
    'pointer : TIMES type_qualifier_list'
    pass


def p_pointer_2(p):
    'pointer : TIMES'
    pass


def p_pointer_3(p):
    'pointer : TIMES type_qualifier_list pointer'
    pass


def p_pointer_4(p):
    'pointer : TIMES pointer'
    pass

# type-qualifier-list:


def p_type_qualifier_list_1(p):
    'type_qualifier_list : type_qualifier'
    pass


def p_type_qualifier_list_2(p):
    'type_qualifier_list : type_qualifier_list type_qualifier'
    pass

# parameter-type-list:


def p_parameter_type_list_1(p):
    'parameter_type_list : parameter_list'
    p[0] = p[1]


def p_parameter_type_list_2(p):
    'parameter_type_list : parameter_list COMMA ELLIPSIS'
    pass

# parameter-list:


def p_parameter_list_1(p):
    'parameter_list : parameter_declaration'
    p[0] = [p[1]]


def p_parameter_list_2(p):
    'parameter_list : parameter_list COMMA parameter_declaration'
    p[0] = p[1] + [p[3]]

# parameter-declaration:


def p_parameter_declaration_1(p):
    'parameter_declaration : declaration_specifiers declarator'
    p[0] = p[2]


def p_parameter_declaration_2(p):
    'parameter_declaration : declaration_specifiers abstract_declarator_opt'
    pass

# identifier-list:


def p_identifier_list_1(p):
    'identifier_list : ID'
    pass


def p_identifier_list_2(p):
    'identifier_list : identifier_list COMMA ID'
    pass

# initializer:


def p_initializer_1(p):
    'initializer : assignment_expression'
    p[0] = p[1]


def p_initializer_2(p):
    '''initializer : LBRACE initializer_list RBRACE
                   | LBRACE initializer_list COMMA RBRACE'''
    pass

# initializer-list:


def p_initializer_list_1(p):
    'initializer_list : initializer'
    pass


def p_initializer_list_2(p):
    'initializer_list : initializer_list COMMA initializer'
    pass

# type-name:


def p_type_name(p):
    'type_name : specifier_qualifier_list abstract_declarator_opt'
    pass


def p_abstract_declarator_opt_1(p):
    'abstract_declarator_opt : empty'
    pass


def p_abstract_declarator_opt_2(p):
    'abstract_declarator_opt : abstract_declarator'
    pass

# abstract-declarator:


def p_abstract_declarator_1(p):
    'abstract_declarator : pointer '
    pass


def p_abstract_declarator_2(p):
    'abstract_declarator : pointer direct_abstract_declarator'
    pass


def p_abstract_declarator_3(p):
    'abstract_declarator : direct_abstract_declarator'
    pass

# direct-abstract-declarator:


def p_direct_abstract_declarator_1(p):
    'direct_abstract_declarator : LPAREN abstract_declarator RPAREN'
    pass


def p_direct_abstract_declarator_2(p):
    'direct_abstract_declarator : direct_abstract_declarator LBRACKET constant_expression_opt RBRACKET'
    pass


def p_direct_abstract_declarator_3(p):
    'direct_abstract_declarator : LBRACKET constant_expression_opt RBRACKET'
    pass


def p_direct_abstract_declarator_4(p):
    'direct_abstract_declarator : direct_abstract_declarator LPAREN parameter_type_list_opt RPAREN'
    pass


def p_direct_abstract_declarator_5(p):
    'direct_abstract_declarator : LPAREN parameter_type_list_opt RPAREN'
    pass

# Optional fields in abstract declarators


def p_constant_expression_opt_1(p):
    'constant_expression_opt : empty'
    pass


def p_constant_expression_opt_2(p):
    'constant_expression_opt : constant_expression'
    pass


def p_parameter_type_list_opt_1(p):
    'parameter_type_list_opt : empty'
    pass


def p_parameter_type_list_opt_2(p):
    'parameter_type_list_opt : parameter_type_list'
    pass

# statement:


def p_statement(p):
    '''
    statement : labeled_statement
              | expression_statement
              | compound_statement
              | selection_statement
              | iteration_statement
              | jump_statement
              '''
    p[0] = p[1]

# labeled-statement:


def p_labeled_statement_1(p):
    'labeled_statement : ID COLON statement'
    p[0] = p[3]


def p_labeled_statement_2(p):
    'labeled_statement : CASE constant_expression COLON statement'
    pass


def p_labeled_statement_3(p):
    'labeled_statement : DEFAULT COLON statement'
    pass

# expression-statement:


def p_expression_statement(p):
    'expression_statement : expression_opt SEMI'
    p[0] = p[1]

# compound-statement:


def p_compound_statement_1(p):
    'compound_statement : LBRACE declaration_list statement_list RBRACE'
    p[0] = p[2] + p[3]


def p_compound_statement_2(p):
    'compound_statement : LBRACE statement_list RBRACE'
    p[0] = p[2]

def p_compound_statement_3(p):
    'compound_statement : LBRACE declaration_list RBRACE'
    p[0] = p[2]


def p_compound_statement_4(p):
    'compound_statement : LBRACE RBRACE'
    pass

# statement-list:


def p_statement_list_1(p):
    'statement_list : statement'
    if utils.is_for_iteration(p[1]):
        p[0] = [[p[1][-1]], ('iteration',) + p[1][1:-1]]
    elif isinstance(p[1], list):
        p[0] = p[1]
    else:
        p[0] = [p[1]]


def p_statement_list_2(p):
    'statement_list : statement_list statement'
    p[0] = p[1] + [p[2]]

# selection-statement


def p_selection_statement_1(p):
    'selection_statement : IF LPAREN expression RPAREN statement'
    true_branch = []
    false_branch = []
    statements = p[5]
    if not isinstance(p[5], list):
        statements = [p[5]]
    for statement in statements:
        if utils.is_assignment(statement): # assignment
            true_branch.append(statement)
        elif utils.is_return(statement):
            true_branch.append(statement)
        elif utils.is_assertion(statement):
            true_branch.append(statement)
        elif isinstance(statement, tuple): # function call
            pass
    for x in {s[1] for s in true_branch if s[0] == 'assignment'}:
        false_branch.append(utils.create_assignment(x, x))
    p[0] = ('selection', true_branch, false_branch, p[3])


def p_selection_statement_2(p):
    'selection_statement : IF LPAREN expression RPAREN statement ELSE statement '
    true_branch = []
    false_branch = []
    true_statements = p[5]
    false_statements = p[7]
    all_variables = set()
    if not isinstance(p[5], list):
        true_statements = [p[5]]
    if not isinstance(p[7], list):
        false_statements = [p[7]]
    for branch, statements in zip((true_branch, false_branch), (true_statements, false_statements)):
        for statement in statements:
            if utils.is_assignment(statement): # assignment
                all_variables.add(utils.get_assignment_lhs(statement))
                branch.append(statement)
            elif isinstance(statement, tuple): # function call
                pass
    for branch in (true_branch, false_branch):
        for var in all_variables - {s[1] for s in branch if s[0] == 'assignment'}:
            branch.append(utils.create_assignment(var, var))
    if utils.is_selection(p[7]):
        p[0] = ('selection', true_branch, p[7], p[3])
    else:
        p[0] = ('selection', true_branch, false_branch, p[3])



def p_selection_statement_3(p):
    'selection_statement : SWITCH LPAREN expression RPAREN statement '
    pass

# iteration_statement:


def p_iteration_statement_1(p):
    'iteration_statement : WHILE LPAREN expression RPAREN statement'
    _, assignments, loop_guard, assertion = utils.analyze_loop(p[3], p[5])
    p[0] = ('iteration', assertion, *assignments, loop_guard)


def p_iteration_statement_2(p):
    'iteration_statement : FOR LPAREN expression_opt SEMI expression_opt SEMI expression_opt RPAREN statement '
    _, assignments, loop_guard, assertion = utils.analyze_loop(p[5], p[9])
    for s in assignments[0]:
        s[utils.get_assignment_lhs(p[7])] = utils.get_assignment_rhs(p[7])
    p[0] = ('for-iteration', assertion, *assignments, loop_guard, p[3])

def p_iteration_statement_3(p):
    'iteration_statement : DO statement WHILE LPAREN expression RPAREN SEMI'
    pass

# jump_statement:


def p_jump_statement_1(p):
    'jump_statement : GOTO ID SEMI'
    pass


def p_jump_statement_2(p):
    'jump_statement : CONTINUE SEMI'
    pass


def p_jump_statement_3(p):
    'jump_statement : BREAK SEMI'
    pass


def p_jump_statement_4(p):
    'jump_statement : RETURN expression_opt SEMI'
    p[0] = ('return', p[2])


def p_expression_opt_1(p):
    'expression_opt : empty'
    pass


def p_expression_opt_2(p):
    'expression_opt : expression'
    p[0] = p[1]

# expression:


def p_expression_1(p):
    'expression : assignment_expression'
    p[0] = p[1]


def p_expression_2(p):
    'expression : expression COMMA assignment_expression'
    pass

# assigment_expression:


def p_assignment_expression_1(p):
    'assignment_expression : conditional_expression'
    p[0] = p[1]


def p_assignment_expression_2(p):
    'assignment_expression : unary_expression assignment_operator assignment_expression'
    if p[2] == '=':
        p[0] = ('assignment', p[1], p[3])
    elif p[2] == '+=':
        p[0] = ('assignment', p[1], p[1] + p[3])
    elif p[2] == '-=':
        p[0] = ('assignment', p[1], p[1] - p[3])
    elif p[2] == '*=':
        p[0] = ('assignment', p[1], p[1] * p[3])

# assignment_operator:


def p_assignment_operator(p):
    '''
    assignment_operator : EQUALS
                        | TIMESEQUAL
                        | DIVEQUAL
                        | MODEQUAL
                        | PLUSEQUAL
                        | MINUSEQUAL
                        | LSHIFTEQUAL
                        | RSHIFTEQUAL
                        | ANDEQUAL
                        | OREQUAL
                        | XOREQUAL
                        '''
    p[0] = p[1]

# conditional-expression


def p_conditional_expression_1(p):
    'conditional_expression : logical_or_expression'
    p[0] = p[1]


def p_conditional_expression_2(p):
    'conditional_expression : logical_or_expression CONDOP expression COLON conditional_expression '
    pass

# constant-expression


def p_constant_expression(p):
    'constant_expression : conditional_expression'
    p[0] = p[1]

# logical-or-expression


def p_logical_or_expression_1(p):
    'logical_or_expression : logical_and_expression'
    p[0] = p[1]


def p_logical_or_expression_2(p):
    'logical_or_expression : logical_or_expression LOR logical_and_expression'
    p[0] = sp.Or(p[1], p[3])

# logical-and-expression


def p_logical_and_expression_1(p):
    'logical_and_expression : inclusive_or_expression'
    p[0] = p[1]


def p_logical_and_expression_2(p):
    'logical_and_expression : logical_and_expression LAND inclusive_or_expression'
    p[0] = sp.And(p[1], p[3])

# inclusive-or-expression:


def p_inclusive_or_expression_1(p):
    'inclusive_or_expression : exclusive_or_expression'
    p[0] = p[1]


def p_inclusive_or_expression_2(p):
    'inclusive_or_expression : inclusive_or_expression OR exclusive_or_expression'
    p[0] = sp.Or(p[1], p[3])

# exclusive-or-expression:


def p_exclusive_or_expression_1(p):
    'exclusive_or_expression :  and_expression'
    p[0] = p[1]


def p_exclusive_or_expression_2(p):
    'exclusive_or_expression :  exclusive_or_expression XOR and_expression'
    pass

# AND-expression


def p_and_expression_1(p):
    'and_expression : equality_expression'
    p[0] = p[1]


def p_and_expression_2(p):
    'and_expression : and_expression AND equality_expression'
    pass


# equality-expression:
def p_equality_expression_1(p):
    'equality_expression : relational_expression'
    p[0] = p[1]


def p_equality_expression_2(p):
    'equality_expression : equality_expression EQ relational_expression'
    p[0] = sp.Eq(p[1], p[3])


def p_equality_expression_3(p):
    'equality_expression : equality_expression NE relational_expression'
    p[0] = sp.Ne(p[1], p[3])


# relational-expression:
def p_relational_expression_1(p):
    'relational_expression : shift_expression'
    p[0] = p[1]


def p_relational_expression_2(p):
    'relational_expression : relational_expression LT shift_expression'
    p[0] = p[1] < p[3]
    # p[0] = PolyCondition(p[1] - p[3], strict=True)


def p_relational_expression_3(p):
    'relational_expression : relational_expression GT shift_expression'
    p[0] = p[1] > p[3]
    # p[0] = PolyCondition(p[3] - p[1], strict=True)


def p_relational_expression_4(p):
    'relational_expression : relational_expression LE shift_expression'
    p[0] = p[1] <= p[3]
    # p[0] = PolyCondition(p[1] - p[3], strict=False)


def p_relational_expression_5(p):
    'relational_expression : relational_expression GE shift_expression'
    p[0] = p[1] >= p[3]
    # p[0] = PolyCondition(p[3] - p[1], strict=False)

# shift-expression


def p_shift_expression_1(p):
    'shift_expression : additive_expression'
    p[0] = p[1]


def p_shift_expression_2(p):
    'shift_expression : shift_expression LSHIFT additive_expression'
    pass


def p_shift_expression_3(p):
    'shift_expression : shift_expression RSHIFT additive_expression'
    pass

# additive-expression


def p_additive_expression_1(p):
    'additive_expression : multiplicative_expression'
    p[0] = p[1]


def p_additive_expression_2(p):
    'additive_expression : additive_expression PLUS multiplicative_expression'
    p[0] = p[1] + p[3]


def p_additive_expression_3(p):
    'additive_expression : additive_expression MINUS multiplicative_expression'
    p[0] = p[1] - p[3]

# multiplicative-expression


def p_multiplicative_expression_1(p):
    'multiplicative_expression : cast_expression'
    p[0] = p[1]


def p_multiplicative_expression_2(p):
    'multiplicative_expression : multiplicative_expression TIMES cast_expression'
    p[0] = p[1] * p[3]


def p_multiplicative_expression_3(p):
    'multiplicative_expression : multiplicative_expression DIVIDE cast_expression'
    p[0] = p[1] / p[3]
    # pass


def p_multiplicative_expression_4(p):
    'multiplicative_expression : multiplicative_expression MOD cast_expression'
    p[0] = p[1] % p[3]

# cast-expression:


def p_cast_expression_1(p):
    'cast_expression : unary_expression'
    p[0] = p[1]


def p_cast_expression_2(p):
    'cast_expression : LPAREN type_name RPAREN cast_expression'
    pass

# unary-expression:


def p_unary_expression_1(p):
    'unary_expression : postfix_expression'
    p[0] = p[1]


def p_unary_expression_2(p):
    'unary_expression : PLUSPLUS unary_expression'
    pass


def p_unary_expression_3(p):
    'unary_expression : MINUSMINUS unary_expression'
    pass


def p_unary_expression_4(p):
    'unary_expression : unary_operator cast_expression'
    if p[1] == '+':
        p[0] = p[2]
    elif p[1] == '-':
        p[0] = -p[2]
    elif p[1] == '!':
        p[0] = sp.Not(p[2])

def p_unary_expression_5(p):
    'unary_expression : SIZEOF unary_expression'
    pass


def p_unary_expression_6(p):
    'unary_expression : SIZEOF LPAREN type_name RPAREN'
    pass

# unary-operator


def p_unary_operator(p):
    '''unary_operator : AND
                    | TIMES
                    | PLUS 
                    | MINUS
                    | NOT
                    | LNOT '''
    p[0] = p[1]

# postfix-expression:


def p_postfix_expression_1(p):
    'postfix_expression : primary_expression'
    p[0] = p[1]


def p_postfix_expression_2(p):
    'postfix_expression : postfix_expression LBRACKET expression RBRACKET'
    pass


def p_postfix_expression_3(p):
    'postfix_expression : postfix_expression LPAREN argument_expression_list RPAREN'
    p[0] = ('call', p[1], ) + p[3]


def p_postfix_expression_4(p):
    'postfix_expression : postfix_expression LPAREN RPAREN'
    global tmp_num
    if p[1].name.startswith('__VERIFIER_nondet_'):
        symbol = sp.Symbol('tmp%d' % tmp_num)
        temp_variables.add(symbol)
        tmp_num += 1
        p[0] = symbol
        if p[1].name.endswith('uint'):
            temp_variables_type[symbol] = 'uint'
        else:
            temp_variables_type[symbol] = 'int'
    else:
        p[0] = ('call', p[1])


def p_postfix_expression_5(p):
    'postfix_expression : postfix_expression PERIOD ID'
    pass


def p_postfix_expression_6(p):
    'postfix_expression : postfix_expression ARROW ID'
    pass


def p_postfix_expression_7(p):
    'postfix_expression : postfix_expression PLUSPLUS'
    p[0] = ('assignment', p[1], p[1] + 1)


def p_postfix_expression_8(p):
    'postfix_expression : postfix_expression MINUSMINUS'
    p[0] = ('assignment', p[1], p[1] - 1)

# primary-expression:


def p_primary_expression_1(p):
    '''primary_expression : ID'''
    p[0] = sp.Symbol(p[1])
    variables.setdefault(sp.Symbol(p[1]), 0)

def p_primary_expression_2(p):
    '''primary_expression : constant
                          |  SCONST
                          |  LPAREN expression RPAREN'''
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = p[2]

# argument-expression-list:


def p_argument_expression_list(p):
    '''argument_expression_list :  assignment_expression
                              |  argument_expression_list COMMA assignment_expression'''
    if len(p) == 2:
        p[0] = (p[1], )
    else:
        p[0] = p[1] + (p[3], )

# constant:


def p_constant(p):
    '''constant : ICONST
               | FCONST
               | CCONST'''
    # s = p[1]
    # if p[1].startswith('0x'):
    #     s = int
    p[0] = sp.Integer(p[1])


def p_empty(p):
    'empty : '
    pass


def p_error(p):
    print('Syntax error %s' % p)
    # print("Whoa. We're hosed")

# Build the grammar
parser = yacc.yacc()

def empty_func():
    # pass
    print('timeout')

tot = 0
correct = 0
unknown = 0
import json
with open('config.json') as fp:
    config = json.load(fp)
@utils.set_timeout(config['timeout'], empty_func)
def check(filename, debug=False):
    global init_num
    global tmp_num
    global variables
    global temp_variables
    global tested_filename
    global N_index
    global correct
    global tot
    global unknown
    global temp_variables_type
    global z3query
    global assertion
    # global exception_path
    # global standard_path
    # standard_path = 'loop/'
    assertion = ''
    z3query = ''
    tested_filename = filename
    N_index = 0
    init_num = 0
    tmp_num = 0
    variables = {}
    temp_variables = set()
    temp_variables_type = {}
    tot += 1
    is_correct = False
    clean()
    with open(filename) as fp:
        print(filename + ': ', end='')
        if not debug:
            try:
                parser.parse(fp.read(), lexer=clexer.lexer)
                res = utils.z3query(z3query, assertion)
                if str(res) == 'unknown':
                    res = utils.z3query(z3query, assertion, neg=True)
                    if str(res) == 'sat':
                        res = 'unsat'
                    elif str(res) == 'unsat':
                        res = 'sat'
                    else:
                        res = 'unknown'
                # answer_path = os.path.join(standard_path, os.path.basename(os.path.split(filename)[0]), os.path.basename(filename).replace('.c', '.yml'))
                # answer = utils.read_answer(answer_path)
                # if (answer and str(res) == 'unsat') or (not answer and str(res) == 'sat'):
                #     is_correct = True
                #     print('correct')
                #     correct += 1
                # elif str(res) == 'unknown':
                #     print('unknown')
                #     unknown += 1
                # else:
                #     print('wrong')
            except Exception as e:
                res = 'unknown'
                # exception_file = os.path.join(exception_path, os.path.basename(filename))
                # print('unknown')
                # with open(os.path.join(exception_path, os.path.basename(filename)), 'w') as ff:
                #     ff.write(str(e))
        else:
            parser.parse(fp.read(), lexer=clexer.lexer)
            res = utils.z3query(z3query, assertion)
    # if not is_correct:
    #     with open('incorrect', 'a') as fp:
    #         fp.write(filename + '\n')
        # print('complete')
    from PRS.mathematica_manipulation import session
    session.terminate()
    return res

# def test_main():
#     # global init_num
#     # global tmp_num
#     # global variables
#     global experiment
#     experiment = True
#     folders = [extracted_recurrence_path, closed_form_solution, exception_path, queries_path]
#     for folder in folders:
#         if os.path.exists(folder):
#             shutil.rmtree(folder)
#         os.mkdir(folder)
#     for path, _, filenames in os.walk('benchmarks/experiment/'):
#         for filename in sorted(filenames):
#             if filename in ['sumt%d.c' % i for i in (7, 8, 9)]: continue
#             check(os.path.join(path, filename))
#             with open(os.path.join(queries_path, filename), 'w') as fp:
#                 fp.write(z3query)
#     times = [row[1] for row in stats]
#     avg = sum(times) / len(times)
#     min_time = min(times)
#     max_time = max(times)
#     stats[0][2] = avg
#     stats[0][3] = min_time
#     stats[0][4] = max_time
#     with open('result.csv', 'w') as fp:
#         f_csv = csv.writer(fp)
#         f_csv.writerow(headers)
#         f_csv.writerows(stats)
#     experiment = False

# if __name__ == '__main__':
#     test_main()
    # print('%d/%d/%d' % (correct, unknown, tot - correct - unknown))
    # with open('benchmarks/support/gsv.c') as fp:
    # check('benchmarks/experiment/loop-acceleration/simple_1-2.c', debug=False)
    # with open('benchmarks/experiment/loop-invariants/eq2.c') as fp:
    # # # with open('loop/loops-crafted-1/Mono6_1.c') as fp:
    #     source = fp.read()
    #     parser.parse(source, lexer=clexer.lexer)
        # res = utils.z3query(z3query)
        # print(res)