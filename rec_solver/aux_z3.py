import z3
def Mod(lhs, rhs):
    return lhs % rhs

def Eq(lhs, rhs):
    return lhs == rhs
   

def DiscreteDelta(x):
    return z3.If(x == 0, 1, 0)

def Heaviside(x):
    return z3.If(x >= 0, 1, 0)