from numpy import isin
import sympy as sp
from importlib import reload
import subprocess
import re

import signal
import time
import yaml

def mul_str(self):
    if isinstance(self.args[0], int) or isinstance(self.args[0], sp.Integer):
        return 'RealVal(%s)*%s'
    if isinstance(self.args[1], int) or isinstance(self.args[1], sp.Integer):
        return 'RealVal(%s)*%s'
    if isinstance(self.args[0], int) or isinstance(self.args[0], sp.Integer):
        return 'RealVal(%s)*%s'
    if isinstance(self.args[0], int) or isinstance(self.args[0], sp.Integer):
        return 'RealVal(%s)*%s'
    if isinstance(self.args[0], int) or isinstance(self.args[0], sp.Integer):
        return 'RealVal(%s)*%s'
    if isinstance(self.args[0], int) or isinstance(self.args[0], sp.Integer):
        return 'RealVal(%s)*%s'
    if isinstance(self.args[0], int) or isinstance(self.args[0], sp.Integer):
        return 'RealVal(%s)*%s'
    if isinstance(self.args[0], int) or isinstance(self.args[0], sp.Integer):
        return 'RealVal(%s)*%s'
    if isinstance(self.args[0], int) or isinstance(self.args[0], sp.Integer):
        return 'RealVal(%s)*%s'
    if isinstance(self.args[0], int) or isinstance(self.args[0], sp.Integer):
        return 'RealVal(%s)*%s'
  
assert_call = '__VERIFIER_assert'
def set_timeout(num, callback):
  def wrap(func):
    def handle(signum, frame):
      raise RuntimeError
  
    def to_do(*args, **kwargs):
      try:
        signal.signal(signal.SIGALRM, handle)
        signal.alarm(num)
        r = func(*args, **kwargs)
        signal.alarm(0)
        return r
      except RuntimeError as e:
        callback()

  
    return to_do
  
  return wrap

def to_PRS(inits, recurrence):
    res = ''.join('%s = %s;\n' % (var, inits[var]) for var in inits) + '\n'
    conds = {}
    # print(recurrence[0][0])
    if recurrence[1][0] == True:
        body = ''.join('%s = %s;\n' % (var, recurrence[0][0][var]) for var in recurrence[0][0])
        res += r'if (true) {%s}' % body
    else:
        for body, cond in zip(*recurrence):
            if isinstance(cond, sp.Eq):
                if isinstance(cond.lhs, sp.Mod):
                    res += 'if (%s) {\n%s} else ' % ('%s %% %s == %s' % (cond.lhs.args[0], cond.lhs.args[1], cond.rhs), dict2c(body))
                else:
                    res += 'if (%s) {\n%s} else ' % ('%s == %s' % (cond.lhs, cond.rhs), dict2c(body))
            else:
                res += 'if (%s) {\n%s} else ' % (cond, dict2c(body))
        res += '{\n%s}' % dict2c(recurrence[0][-1])
    return res

def dict2c(d):
    return ''.join('%s = %s;\n' % (k, d[k]) for k in d)

def z3query(axioms, assertion, neg=False):
    with open('z3q.py', 'w') as fp:
        fp.write(axioms)
        fp.write('def query():\n')
        fp.write('    global s\n')
        # fp.write('    solver = Solver()\n')
        if not neg:
            fp.write('    s.add(Not(%s))\n' % assertion)
        else:
            fp.write('    s.add(%s)\n' % assertion)
        fp.write('    res = solver.check(s)\n')
        # fp.write('    s = set()\n')
        fp.write('    return res\n')
        fp.write('print(query())')
    out = subprocess.check_output(['python', 'z3q.py']).decode().strip()
    return out

def closed_form2z3(closed_form, order, var, index):
    conds, closed = closed_form[0], closed_form[1]
    # print(conds)
    closed_form_index = order.index(var)
    res = 'If(%s, %s, %s)'
    lcm = 1
    for i in range(len(conds)):
        for j in range(len(closed[i])):
            # print(closed)
            together = sp.together(closed[i][j][closed_form_index])
            if isinstance(together, sp.Mul) and isinstance(together.args[0], sp.Rational):
                de = 1/together.args[0]
                lcm = sp.lcm(lcm, de)
    for i in range(len(conds)-1):
        cond_str = 'And(%s <= %s, %s < %s)' % (conds[i], index, index, conds[i+1])
        if i < len(conds) - 2:
            res = res % (cond_str, closed_form2mod(closed[i], closed_form_index, index, lcm), 'If(%s, %s, %s)')
            # res = res % (cond_str, closed[i][closed_form_index], 'If(%s, %s, %s)')
        else:
            res = res % (cond_str, closed_form2mod(closed[i], closed_form_index, index, lcm), '%s')
            # res = res % (cond_str, closed[i][closed_form_index], '%s')
    if len(conds) == 1:
        res = closed_form2mod(closed[0], closed_form_index, index, lcm)
        # res = closed[0][closed_form_index]
    else:
        res = res % closed_form2mod(closed[-1], closed_form_index, index, lcm)
        # res = res % closed[-1][closed_form_index]
    # print(res)
    return lcm, res
        # res = res % ('And(%s <= %s, %s <  %s)' % (conds[i]))

def repl(matchobj):
    return 'RealVal(%s)' % matchobj.group(0)

def closed_form2mod(closed_form, var_index, index, multiple):
    res = 'If(Mod(%s, %d) == %d, %s, %s)'
    num = len(closed_form)
    for i in range(num - 1):
        closed_form_z3 = str(multiple*closed_form[i][var_index])
        # closed_form_z3 = re.sub(r'\d+', repl, str(multiple*closed_form[i][var_index]))
        if i < num - 2:
            res = res % (index, num, i, closed_form_z3, 'If(Mod(%s, %d) == %d, %s, %s)')
        else:
            res = res % (index, num, i, closed_form_z3, '%s')
    if num == 1:
        # res = re.sub(r'\d+', repl, str(multiple*closed_form[0][var_index]))
        res = str(multiple*closed_form[0][var_index])
        # res = str(closed_form[0][var_index])
    else:
        res = res % str(multiple*closed_form[num-1][var_index])
        # res = res % re.sub(r'\d+', repl, str(multiple*closed_form[num-1][var_index]))
        # res = res % closed_form[num-1][var_index]
    return res

def analyze_loop(loop_guard, loop_body):
    assignments = [[{}, {}], [sp.true]]
    it = 0
    assertion = None
    for statement in loop_body:
        it += 1
        if is_assignment(statement):
            lhs = get_assignment_lhs(statement)
            rhs = get_assignment_rhs(statement)
            for branch in assignments[0]:
                updated = rhs.subs(branch, simultaneous=True)
                branch[lhs] = updated
        elif is_selection(statement):
            try:
                (t_branch, f_branch), cond = selection_bodies_conds(statement)
                if len(t_branch) == 1 and is_assertion(t_branch[0]):
                    _, assertion = function_name_args(t_branch[0])
                    assertion = assertion[0], it == len(loop_body)
                    continue
            except:
                pass
            # print(assignments[1][0])
            if assignments[1][0]:
                values = assignments[0][0]
                bodies_conds = selection_bodies_conds(statement)
                new_bodies = []
                new_conds = []
                for seq_body in bodies_conds[0]:
                    body = sequence2parallel(seq_body)
                    for var in body:
                        body[var] = body[var].subs(values)
                    for var in values:
                        if var not in body:
                            body[var] = values[var]
                    new_bodies.append(body)
                for i, cond in enumerate(bodies_conds[1]):
                    new_conds.append(cond.subs(values))
                assignments = new_bodies, new_conds
            else:
                raise Exception('Only one sequence of if-else is supported now')
        elif is_assertion(statement):
            _, assertion = function_name_args(statement)
            assertion = assertion[0], it == len(loop_body)
        # elif is_assertion(statement):
        #     print(statement)
    involved_variables = set()
    for body in assignments[0]:
        for var in body:
            involved_variables.add(var)
    for body in assignments[0]:
        for var in involved_variables:
            if var not in body:
                body[var] = var

    return ('iteration', assignments, sp.true if loop_guard == 1 else loop_guard, assertion)

def read_answer(filename):
    with open(filename) as fp:
        yml = yaml.load(fp, Loader=yaml.FullLoader)
    properties = yml['properties']
    for prop in properties:
        if 'unreach-call' in prop['property_file'] or 'no-overflow' in prop['property_file']:
            return prop['expected_verdict']
    else:
        print('property not found')

def get_assertion_in_loop(statement):
    return statement[1]

def is_assertion(statement):
    name, *args = function_name_args(statement)
    try:
        return name.name == assert_call
    except:
        return False

def is_return(statement):
    try:
        return statement[0] == 'return'
    except:
        return False

def is_assignment(statement):
    return statement[0] == 'assignment'

def is_assignment_list(statement):
    return statement[0][0] == 'assignment'

def is_iteration(statement):
    return statement[0] == 'iteration'

def is_for_iteration(statement):
    return statement[0] == 'for-iteration'

def is_selection(statement):
    return statement[0] == 'selection'

def is_function_call(statement):
    return statement[0] == 'call'

def function_name_args(statement):
    if len(statement) > 2:
        return statement[1], statement[2:]
    else:
        return (statement[1],)

def relation2str(relation):
    if isinstance(relation, sp.Eq) and isinstance(relation.lhs, sp.Mod):
        return '%s == %s' % (relation.lhs, relation.rhs)
    if isinstance(relation, sp.Eq):
        return '%s == %s' % (relation2str(relation.lhs), relation2str(relation.rhs))
    elif isinstance(relation, sp.Ne):
        return '%s != %s' % (relation2str(relation.lhs), relation2str(relation.rhs))
    elif isinstance(relation, sp.Mod):
        return '%s > 0' % relation
    else:
        return str(relation)

def assignment2dict(assignment):
    return {assignment[1]: assignment[2]}

def get_assignment_lhs(assignment):
    return assignment[1]

def get_assignment_rhs(assignment):
    return assignment[2]

def get_selection_cond(selection):
    return selection[3]

def create_assignment(lhs, rhs):
    return ('assignment', lhs, rhs)

def selection_bodies_conds(selection):
    if len(selection[2]) == 0 or selection[2][0] != 'selection':
        return [selection[1], selection[2]], [selection[3]]
    else_branch = selection_bodies_conds(selection[2])
    return [selection[1]] + else_branch[0], [selection[3]] + else_branch[1]

def sequence2parallel(sequence):
    values = {}
    for i, statement in enumerate(sequence):
        lhs = get_assignment_lhs(statement)
        rhs = get_assignment_rhs(statement)
        rhs = rhs.subs(values, simultaneous=True)
        values[lhs] = rhs
    return values
