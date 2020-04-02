/- Author: E.W.Ayers  -/

instance : has_repr name := ⟨λ x, to_string x⟩

meta def hello_override := `hello_override.name

@[vm_override hello_override]        -- this means that the VM should replace the definition of `hello` with `hello_override` when evaluating.
meta def hello := `hello.name

#print hello                         -- should use `hello

#eval hello                          -- should be `hello_override

set_option vm_override.enabled false -- now the VM should ignore all overrides

#eval hello                          -- should be `hello

@[vm_override hello_override]
meta def hello_2 := `hello_2.name

#eval hello_2                        -- should be `hello_2 because vm_overrides are not enabled

set_option vm_override.enabled true

#eval hello_2 -- should be `hello_override

/- When overriding an inductive datatype, you need to provide two arguments.
The first argument says what the type should be replaced with and the second argument says where
the overridden recursors and constructors are.

To test that vm_override works with inductive definitions we are going to introduce some
dummy inductive non-meta definitions of `float` and then override them with the meta `native.float`.

So this test file also indicates the danger of using vm_overrides, because it can mean that the VM evaluation and the
kernel evaluation of a lean expression can be different.

VM overriding also gives the user the ability to 'monkey patch' definitions in core.
-/

-- should fail; `unknown declaration native.float.mk`
@[vm_override native.float native.float]
inductive float₀ : Type 1
| mk : ℕ → float₀

namespace native.float₁

meta def mk :  ℕ → native.float := sorry

-- Note that this has the wrong type to be an override of `float₁.rec`.
meta def rec : ℕ := 3

end native.float₁

-- should fail: 'type mismatch with override'
@[vm_override native.float native.float₁]
inductive float₁ : Type 1
| mk : ℕ → float₁

namespace  native.float

meta def mk :  ℕ → native.float
| n := n

meta def rec {C : native.float → Sort*} (f : Π (a : ℕ), C (native.float.mk a)) (n : native.float) : C n := sorry

meta def cases_on {C : native.float → Sort*} (n : native.float) (f : Π (a : ℕ), C (native.float.mk a)) : C n := sorry

end native.float

@[vm_override native.float native.float]
inductive float : Type 1
| mk : ℕ → float

@[vm_override native.float.add]
def add : float → float → float
| (float.mk x) (float.mk y) := float.mk (x + y)

instance : has_add float := ⟨add⟩

@[vm_override native.float.div]
def div : float → float → float
| (float.mk x) (float.mk y) := float.mk 5

instance : has_div float := ⟨div⟩

@[vm_override native.float.pow]
def float.pow : float → float → float
| (float.mk a) (float.mk b) := float.mk $ nat.cases_on b 1 (λ x, a * x)

instance : has_pow float float := ⟨float.pow⟩

@[vm_override native.float.zero]
def zero : float := float.mk 0

def one : float := float.mk 1

@[vm_override native.float.has_one]
instance float.has_one : has_one float := ⟨one⟩

instance : has_zero float := ⟨zero⟩

@[vm_override native.float.to_repr]
def to_repr (p : float) : string := repr "dummy"

instance : has_repr float := ⟨to_repr⟩

set_option pp.numerals false

#check  (2 : float)

-- our definition of `div` is silly.
example (x y : float) :  x / y = 5 := begin cases x, cases y, refl end

-- but evaluation is using native.float and gives different answers.
#eval (0.1 : float) / (0.2 : float)

#eval (0.1 + 05 / 0.0000034 : float)
