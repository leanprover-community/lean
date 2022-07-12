
open native  native.float

meta def close_enough (a b : float) : bool := abs (a - b) < 10 * epsilon
local infixr ` ≃ `:2 := close_enough

meta def floats := [0,1,-1,pi,epsilon, 1/epsilon, pi / 2, pi / 4, -pi]
meta def floats2 := list.bind floats (λ x, floats.map (λ y, (x,y)))

meta def check1 (prop : float → bool)  := list.map prop floats
meta def check2  (floats : list (float × float))(prop : float → float → bool) :=
list.foldl band tt $ floats.map (λ ⟨x,y⟩, prop x y)

#eval specification.radix
#eval specification.precision
#eval specification.emax
#eval specification.emin
#eval (specification.emax : ℤ) + specification.emin -- [FIXME] should be 1?!

#eval check1 $ λ x, 1 / (1 / x) = x
#eval (1 : float) / 0
#eval epsilon
#eval 1 / epsilon
#eval infinity
#eval 1 / infinity
#eval exponent infinity
#eval exponent epsilon
#eval exponent qNaN
#eval bnot $ sign infinity
#eval - infinity
#eval sign $ - infinity
-- #eval infinity - infinity -- [NOTE] platform dependent
#eval qNaN
#eval sNaN
#eval bnot (qNaN = qNaN : bool) -- [NOTE] not reflexive
#eval (infinity = infinity : bool)
#eval (infinity ≠ -infinity : bool)
#eval is_infinite infinity
#eval is_infinite $ -infinity
#eval bnot $ is_infinite 4
#eval check1 $ is_finite

#eval frexp 123.45
#eval check1 $ λ x, let ⟨a,b⟩ := frexp x in x = a * (2 : float) ^ (b : float)
#eval check1 $ λ x, let ⟨a,b⟩ := modf x in x = a + b
-- #eval frexp qNaN     -- [NOTE] platform dependent
-- #eval frexp infinity -- [NOTE] platform dependent

#eval log 0
#eval log infinity
#eval log epsilon
#eval log (1 / epsilon)

#eval exp (1 / epsilon)
#eval check1 $ λ x, log (exp x) ≃ x
#eval check1 $ λ x, log2 (exp2 x) ≃ x
#eval is_nan (log $ -1)
#eval exp (log pi)
#eval pi ≃ 2 * asin 1
#eval pi ≃ 2 * acos 0
#eval check1 $ λ x, bor (abs x > 1) (cos (acos x) ≃ x)
#eval check1 $ λ x, bor (abs x > 1) (tan (atan x) ≃ x)
#eval check1 $ λ x, sinh (asinh x) ≃ x
#eval check1 $ λ x, bor (x < 1) $ cosh (acosh x) ≃ x
#eval check1 $ λ x, bor (abs x ≥ 1) $ (tanh (atanh x) ≃ x)
#eval check1 $ λ x, asinh (sinh x) ≃ x
#eval check1 $ λ x, acosh (cosh x) ≃ x
#eval abs $ atanh (tanh (-pi)) + pi
#eval (tanh (1/epsilon))
#eval atanh 1
#eval check1 $ λ x, bor (tanh x = 1) $ abs (atanh (tanh x) - x) < 0.1
#eval check1 $ λ x, bor (x ≤ 0) $ log x + (log (1/x)) ≃ 0
#eval check1 $ λ x, (sin x)^2 + (cos x)^2 ≃ 1
#eval check2
  [(0,0), (3,4),(-31,epsilon),(1/epsilon, epsilon)]
  $ λ x y, hypot x y ≃ sqrt(x^2 + y^2)
#eval check1 $ λ x, exp2 (log2 x) ≃ x
#eval check1 $ λ x, log10 x ≃ log x / log 10
#eval check2 floats2 $ λ x y, (x < y) ∨ (y ≤ x)
#eval check2 floats2 $ λ x y, x + y ≃ y + x
#eval check1 $ λ x, abs(x) = max x (-x)
#eval check2
    [(1,2), (5.1, 3), (-1,-1),(-2,pi),(-pi,234),(epsilon,pi)]
    $ λ x y, x = fmod x y + (y * trunc (x / y))
#eval fmod 3 4
#eval sin 0
#eval is_nan $ sin infinity
#eval cos 0
#eval tan 0
#eval sin $ pi / 2
#eval 0 ≃ (cos $ pi / 2)
#eval tan $ pi / 2
#eval 0 ≃ (1 / (tan $ pi / 2))
#eval sin pi ≃ 0
#eval cos pi
#eval tan pi ≃ 0

#eval of_nat 0x100000000  -- 2 ^ 32
#eval of_int 0x100000000  -- 2 ^ 32
#eval of_nat 0x10000000000000000   -- 2 ^ 64
#eval of_int 0x10000000000000000   -- 2 ^ 64

#eval (of_int (-12341234))

#eval to_bool $ float.floor (2.5)  =  2
#eval to_bool $ float.floor (-2.5) = -3
#eval to_bool $ float.ceil  (2.5)  =  3
#eval to_bool $ float.ceil  (-2.5) = -2
#eval to_bool $ float.trunc (2.5)  =  2
#eval to_bool $ float.trunc (-2.5) = -2
#eval to_bool $ float.round (2.5)  =  3
#eval to_bool $ float.round (-2.5) = -3

#eval to_bool $ float.round (of_int 0x100000000) = 0x100000000
#eval to_bool $ float.round (of_int 0x10000000000000000) = 0x10000000000000000

#eval (native.float.infinity : native.float).floor
#eval (native.float.infinity : native.float).ceil
#eval (native.float.infinity : native.float).trunc
#eval (native.float.infinity : native.float).round

#eval (of_string "hello")
#eval (of_string "0.123E4")
#eval (of_string "-123.123")
#eval (of_string "-123.0000000000000000000000000001")
#eval (of_string "-2.28773e+07")