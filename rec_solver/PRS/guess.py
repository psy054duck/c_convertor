import sympy as sp
from .condition import PolyCondition

_x = []
def guess_pattern(A, x0, conds, a, seq, x):
    ''' A problem instance is assumed to be linearly piecewise.
    That is,
              /-- A[0]x(n)   cond[0]
              |   :
              |   :
    x(n+1) = <
              |   :
              |   :
              \-- A[m]x(n)   cond[m]
    This function would find a sequence 'pattern' = <A_{h_{k-1}}, ..., A_{h_{0}}> s.t.
    x(a) = A_{h_{r}...h_{0}(pattern)^q}x(j) with minimum 'j', where a = qk + r, r = 0...k-1.
    
    return j_min, x_{j_min}, pattern
    '''
    seq, x = _convert2seq(A, x0, conds, a, seq, x)
    # print(seq)
    j_min = a
    pattern = None
    # print(seq)
    for i in range(1, len(seq)//2 + 1):
        candidate = seq[0:i]
        j = _covers(candidate, seq)
        if j < j_min:
            j_min, pattern = j, candidate
            # TODO it may be improved by an early break, something like 'if j_min < len(pattern): break'
    res = j_min, x[j_min], pattern, seq[len(seq)-j_min:], seq, x
    return res

def _covers(pattern, seq):
    k = len(pattern)
    for i in range(len(pattern), len(seq)):
        r = i % k
        if pattern[r] != seq[i]:
            if i // k >= 2:
                return len(seq) - i + r
            else:
                return len(seq)
    return (i + 1) % k

def _convert2seq(A, x0, conds, a, seq, x):
    if len(x) == 0:
        x = [x0]
    res = list(reversed(seq))
    # x = [x0]
    # res = []
    num_pieces = len(conds)
    for _ in range(a - len(seq)):
        for j in range(num_pieces):
            # print(conds[j].lhs, conds[j].rhs)
            if conds[j].evaluate({sp.Symbol('_PRS_x%d' % i): x[-1][i] for i in range(len(x0))}):
                res.append(j)
                x.append(A[j]*x[-1])
                break
        else:
            res.append(num_pieces)
            x.append(A[num_pieces]*x[-1])
    return list(reversed(res)), x

    
if __name__ == '__main__':
    from rand_instance import generate_linear_instance
    A, x0, v = generate_linear_instance(2, 2, seed=None)
    _PRS_x0, _PRS_x1 = sp.symbols('_PRS_x0 _PRS_x1')
    res = guess_pattern(A, x0, [PolyCondition(_PRS_x0, strict=False)], 10)
    print(res)