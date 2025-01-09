from .utils import my_simplify
from numpy import isin
import sympy as sp
from sympy.parsing.mathematica import mathematica
from sympy.simplify.simplify import simplify
from wolframclient.language import wl, wlexpr
from wolframclient.evaluation import WolframLanguageSession
import signal
import re
import json
import psutil

with open('rec_solver/config.json') as fp:
    config = json.load(fp)
    import time
    s = time.time()
    process_name = 'WolframKernel'
    for proc in psutil.process_iter():
        if proc.name() == process_name:
            proc.kill()
    session = WolframLanguageSession(config['MathematicaPath'])
    # print(time.time() - s)
# session = WolframLanguageSession('/usr/local/Wolfram/WolframEngine/12.3/Executables/MathKernel')

def exit_interupt(signum, frame):
    session.terminate()
    exit(0)
signal.signal(signal.SIGINT, exit_interupt)

cached_key = []
cached_v = []


translation_rules = {'Plus[*x]': 'Add(*x)',
                     'Power[x, y]': 'Mul(x, Pow(x, y-1))',
                     'Rational[x, y]': 'Rational(x, y)',
                     'Times[*x]': 'Mul(*x)',
                     'Complex[x, y]': 'Add(x, y*I)',
                     'DiscreteDelta[*x]': 'DiscreteDelta(*x)',
                     'UnitStep[*x]': 'Heaviside(*x)',
                     'Piecewise[*x]': 'Piecewise(*x)',
                     'Greater[x, y]': 'x > y',
                     'LessEqual[x, y]': 'x <= y',
                     'NonCommutativeMultiply[x, y]': 'Pow(x, y)',
		             }

def matrix_power_mathematica(m, n):
    global cached_key
    old_n = None
    if isinstance(n, sp.Symbol):
        old_n = n
        n = wl.n
        for i, k in enumerate(cached_key):
            if m == k:
                return cached_v[i]
        cached_key.append(m)
    m = matrix2mathematica(m)
    # print(m)

    # with WolframLanguageSession('/usr/local/Wolfram/WolframEngine/12.3/Executables/MathKernel') as session:
    # res = session.evaluate(wl.FullSimplify(wl.MatrixPower(m, n), wl.Assumptions))
    res = session.evaluate(wl.Assuming(wl.And(wl.Greater(n, 0), wl.Element(n, wl.Integers)), wl.FullSimplify(wl.MatrixPower(m, n))))
    # res = session.evaluate('m = %s' % str(m).replace('[', '{').replace(']', '}'))
    # res = session.evaluate(wlexpr('FullSimplify[MatrixPower[m, n], Assumptions -> n > 0 && Element[n, Integers]]'))
    # print(res)
    # res = session.evaluate(wl.MatrixPower(m, n))
    res = [[t for t in row] for row in res]
    res = matrix2sympy(res)
    # res = res.subs(0**sp.Symbol('n', integer=True), 0)
    # if old_n is not None:
    #     res = res.subs(sp.Symbol('n'), old_n, simultaneous=True)
    if n == wl.n:
        cached_v.append(res)
    return res

def matrix_mul(a, b):
    a_p = matrix2mathematica(a)
    b_p = matrix2mathematica(b)
    # with WolframLanguageSession('/usr/local/Wolfram/WolframEngine/12.3/Executables/MathKernel') as session:
    res = session.evaluate(wl.Dot(a_p, b_p))
    res = [[t for t in row] for row in res]
    res = matrix2sympy(res)
    return res



def obj2mathematica(o):
    if isinstance(o, sp.core.numbers.Zero):
        return 0
    elif isinstance(o, sp.Rational):
        return wl.Rational(o.numerator(), o.denominator())
    elif isinstance(o, sp.Integer):
        return int(o)
    elif isinstance(o, sp.Float):
        return float(o)
    else:
        return wlexpr(str(o))
        raise Exception('unknown type: %s' % type(o))

def matrix2mathematica(m):
    m = m.tolist()
    m = [[obj2mathematica(t) for t in row] for row in m]
    return m

def matrix2sympy(m):
    to_parse = str(m).replace("Global`n", 'n')
    # to_parse = str(m).replace("Global`Heaviside", 'Heaviside')
    # print(to_parse)
    # to_parse = re.sub(r'Power\[0, (^])*\]', '0', to_parse)
    return sp.Matrix(mathematica(to_parse, translation_rules)).subs(sp.Symbol('n'), sp.Symbol('n', integer=True))

def clean():
    global cached_key
    global cached_v
    cached_key = []
    cached_v = []

if __name__ == '__main__':

    n = sp.Symbol('n')
    # res = wlexpr('2*n')
    # print(res)
    # m1 = sp.Matrix([[1, 0], [0, -2]])
    # m2 = sp.Matrix([[1, 0], [0, -2]])
    # res = matrix_mul(m1, m2)
    # print(res)
    # print(matrix_power(m, n))
