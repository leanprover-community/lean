/- Author: E.W.Ayers -/

instance : has_repr name := ⟨λ x, to_string x⟩

meta def hello_override := `hello_override.name

@[vm_override hello_override]
meta def hello := `hello.name

#print hello
#eval hello

set_option vm_override.enabled false

#eval hello

set_option vm_override.enabled true

#eval hello

@[vm_override native.float native.float]
inductive float₀ : Type 1
| mk : ℕ → float₀

namespace native.float₁

meta def mk :  ℕ → native.float := sorry

meta def rec : ℕ := 3

end native.float₁

@[vm_override native.float native.float₁]
inductive float₁ : Type 1
| mk : ℕ → float₁

namespace  native.float

meta def mk :  ℕ → native.float := sorry

meta def rec {C : native.float → Sort*} (f : Π (a : ℕ), C (native.float.mk a)) (n : native.float) : C n := sorry

meta def cases_on {C : native.float → Sort*} (n : native.float) (f : Π (a : ℕ), C (native.float.mk a)) : C n := sorry

end native.float

@[vm_override native.float native.float]
inductive float : Type 1
| mk : ℕ → float

@[vm_override native.float.add]
def add (a b : float) : float := sorry

instance : has_add float := ⟨add⟩

@[vm_override native.float.div]
def div (a b : float) : float := sorry

instance : has_div float := ⟨div⟩

@[vm_override native.float.pow]
def float.pow (a b : float) : float := sorry

instance : has_pow float float := ⟨float.pow⟩

-- @[vm_override native.float.zero]
-- @[vm_override native.float.zero]
def zero : float := sorry

-- @[vm_override native.float.one]
-- @[vm_override native.float.one]
def one : float := sorry

@[vm_override native.float.has_one]
instance float.has_one : has_one float := ⟨one⟩

@[vm_override native.float.has_zero]
instance float.has_zero : has_zero float := ⟨zero⟩

@[vm_override native.float.to_repr]
def to_repr (p : float) : string := repr "dummy"

instance : has_repr float := ⟨to_repr⟩
set_option pp.numerals false
-- #check  (0.1 + 05 / 0.0000034 : float)

#eval (0.1 + 05 / 0.0000034 : float)
