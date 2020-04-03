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

namespace bin_example

namespace bin

inductive pos
| one : pos
| bit0 : pos → pos
| bit1 : pos → pos

def pos.sizeof' : pos → nat
| pos.one := 1
| (pos.bit0 p) := bit0 (pos.sizeof' p)
| (pos.bit1 p) := bit1 (pos.sizeof' p)

instance : has_sizeof pos := ⟨ pos.sizeof' ⟩

inductive nat
| zero : nat
| pos : pos → nat

universes l

namespace pos

def succ : pos → pos
| one := bit0 one
| (bit0 p) := bit1 p
| (bit1 p) := bit0 $ succ p

def pred : pos → pos
| one := one
| (bit0 one) := one
| (bit0 p) := bit1 (pred p)
| (bit1 p) := bit0 p

lemma succ_pred_bit0 : ∀ p : pos, succ (pred $ bit0 p) = bit0 p
| one := rfl
| (bit0 p) :=
  show bit0 _ = _, from
  congr_arg _ (succ_pred_bit0 _)
| (bit1 p) := rfl

lemma succ_pred_bit1 : ∀ p : pos, succ (pred $ bit1 p) = bit1 p
| one := rfl
| (bit0 p) := rfl
| (bit1 p) := rfl

lemma sizeof_pred_bit0_lt : ∀ p : pos, sizeof' (pred (bit0 p)) < sizeof' (bit0 p)
| one := nat.one_lt_bit0 (by dsimp [pos.sizeof]; apply one_ne_zero)
| (bit0 p) :=
  nat.bit1_lt_bit0 $ sizeof_pred_bit0_lt p
| (bit1 p) := nat.bit1_lt_bit0 $ nat.bit0_lt_bit1 $ le_refl _

@[inline]
def rec' {C : bin.pos → Sort l}
  (x₀ : C bin.pos.one)
  (f : ∀ n, C n → C (bin.pos.succ n)) :
  Π (n : bin.pos), C n
| bin.pos.one := x₀
| (bin.pos.bit0 p) :=
  have sizeof' (pred (bit0 p)) < sizeof' (bit0 p),
    from sizeof_pred_bit0_lt _,
  (succ_pred_bit0 p).rec (f _ (rec' _))
| (bin.pos.bit1 p) :=
  have sizeof' (pred (bit1 p)) < sizeof' (bit1 p),
    from nat.bit0_lt_bit1 (le_refl _),
  (succ_pred_bit1 p).rec (f _ (rec' _))

def cases_on' {C : bin.pos → Sort l}
  (x₀ : C bin.pos.one)
  (f : ∀ n, C (bin.pos.succ n)) :
  Π (n : bin.pos), C n
| bin.pos.one := x₀
| (bin.pos.bit0 p) :=
  have sizeof' (pred (bit0 p)) < sizeof' (bit0 p),
    from sizeof_pred_bit0_lt _,
  (succ_pred_bit0 p).rec (f _)
| (bin.pos.bit1 p) :=
  have sizeof' (pred (bit1 p)) < sizeof' (bit1 p),
    from nat.bit0_lt_bit1 (le_refl _),
  (succ_pred_bit1 p).rec (f _)

end pos


namespace nat_ovr

def zero : nat := bin.nat.zero

def succ : nat → nat
| nat.zero := nat.pos pos.one
| (nat.pos p) := nat.pos p.succ

@[inline]
def rec {C : bin.nat → Sort l}
  (x₀ : C bin.nat_ovr.zero)
  (f : ∀ n, C n → C (bin.nat_ovr.succ n)) :
  Π (n : bin.nat), C n
| nat.zero := x₀
| (nat.pos p) := @pos.rec' (λ p, C (nat.pos p)) (f zero x₀) (λ p h, f (nat.pos p) h) _

@[inline]
def cases_on {C : bin.nat → Sort l} (n : bin.nat) (x₀ : C bin.nat_ovr.zero) (x₁ : Π (a : bin.nat), C (bin.nat_ovr.succ a)) : C n :=
match n with
| nat.zero := x₀
| nat.pos p :=
  @pos.cases_on' (λ x, C (nat.pos x))
    (x₁ nat.zero) (λ n, x₁ (nat.pos n)) _
end

def repr' : bin.pos → string
| bin.pos.one := "1"
| (bin.pos.bit0 p) := repr' p ++ "0"
| (bin.pos.bit1 p) := repr' p ++ "1"

def repr : bin.nat → string
| bin.nat.zero := "0"
| (bin.nat.pos p) := repr' p

def add' : bin.pos → bin.pos → bin.pos
| pos.one p := p.succ
| p pos.one := p.succ
| (pos.bit0 p) (pos.bit0 p') := pos.bit0 (add' p p')
| (pos.bit1 p) (pos.bit0 p') := pos.bit1 (add' p p')
| (pos.bit0 p) (pos.bit1 p') := pos.bit1 (add' p p')
| (pos.bit1 p) (pos.bit1 p') := pos.bit0 (add' p p'.succ)

def add : bin.nat → bin.nat → bin.nat
| nat.zero n := n
| n nat.zero := n
| (nat.pos p) (nat.pos p') := nat.pos $ add' p p'

end nat_ovr


end bin

@[vm_override bin.nat bin_example.bin.nat_ovr]
inductive un_nat
| zero : un_nat
| succ : un_nat → un_nat

set_option trace.compiler.inline true

@[vm_override bin_example.bin.nat_ovr.repr]
def repr (i : un_nat) : string := ""

instance : has_repr un_nat := ⟨ repr ⟩

@[vm_override bin_example.bin.nat_ovr.add]
def add (n : un_nat) : un_nat → un_nat
| un_nat.zero := n
| (un_nat.succ m) := un_nat.succ (add m)

def mk_num : ℕ → un_nat
| 0 := un_nat.zero
| (nat.succ n) := add (mk_num n) (mk_num n).succ

def mk_num' : un_nat → un_nat
| un_nat.zero := un_nat.zero
| (un_nat.succ n) := add (mk_num' n) (mk_num' n).succ

#eval mk_num 5
#eval mk_num' un_nat.zero.succ.succ.succ.succ.succ

end bin_example

namespace native.float₃

@[inline]
meta def mk : ℕ → native.float := λ _, 1

@[inline]
meta def {l} rec {C : native.float → Sort l} : (Π (a : ℕ), C (native.float₃.mk a)) → Π (n : native.float), C n :=
λ f n, unchecked_cast (f 1)

@[inline]
meta def {l} cases_on {C : native.float → Sort l} (n : native.float) : (Π (a : ℕ), C (native.float₃.mk a)) → C n:=
λ f, unchecked_cast (f 1)

end native.float₃

@[vm_override native.float native.float₃]
inductive float₃ : Type 1
| mk : ℕ → float₃

set_option trace.compiler.inline true

def float₃.repr : float₃ → string
| ⟨n⟩ := repr n

instance : has_repr float₃ :=
⟨ float₃.repr ⟩

def make : ℕ → float₃ := float₃.mk

#eval make 3

def get₂ : float₃ → ℕ
| (float₃.mk n) := n

#eval get₂ $ make 3

def {l} cases_on : Π {C : float₃ → Sort l} (n : float₃), (Π (a : ℕ), C (float₃.mk a)) → C n:=
@float₃.cases_on

set_option vm_override.enabled false

#eval @cases_on (λ n, ℕ) (float₃.mk 3) (λ n, n)

set_option vm_override.enabled true

#eval @cases_on (λ n, ℕ) (float₃.mk 3) (λ n, n)
#eval @float₃.rec_on (λ n, ℕ) (float₃.mk 3) (λ n, n)
