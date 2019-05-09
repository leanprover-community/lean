
open native  native.float

#eval specification.radix
#eval specification.precision
#eval specification.emax
#eval specification.emin
#eval (specification.emax : ℤ) + specification.emin -- [FIXME] should be 1?

#eval (1 : float) / 0
#eval epsilon
#eval 1 / epsilon
#eval infinity
#eval exponent infinity
#eval exponent epsilon
#eval sign infinity
#eval - infinity
#eval sign $ - infinity
#eval infinity - infinity
#eval qNaN
#eval sNaN
#eval (qNaN = qNaN : bool) -- [TODO] should we be concerned with nonreflexivity?
#eval is_infinite infinity
#eval is_infinite $ -infinity
#eval is_infinite 4