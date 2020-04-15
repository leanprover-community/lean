import init.meta.expr_address

def asdf {P Q : Prop} : P → Q → P ∧ Q :=
begin
  intro p,
  intro q,
  split,
  assumption,
  assumption,
end

meta inductive paf
| pure : format → paf
| pp_expr : expr → paf
-- other hooks may be available

/-
pp_on {α} :
  (format → tactic α) →
  (address → α → tactic α) →
  (list α → tactic α) →
  → expr → tactic α

For simplicity, address is just going to be a linked list of number pairs.
There might already be a path system?

-/

inductive sexpr : Type
| nil : sexpr
| string : string → sexpr
| bool : bool → sexpr
| int : int → sexpr
-- | double : float → sexpr
| name : name → sexpr
| cons : sexpr → sexpr → sexpr
-- | ext : α → sexpr

inductive fmt : Type
| nil : fmt
| text : sexpr → fmt
| choice : fmt → fmt → fmt
| compose : fmt → fmt → fmt
| line : fmt
| nest : nat → fmt → fmt
| highlight : format.color → fmt → fmt

namespace fmt

instance : has_append fmt := ⟨fmt.compose⟩
instance : has_coe string fmt := ⟨text ∘ sexpr.string⟩

def lp : fmt := "("
def rp : fmt := ")"
def group : fmt → fmt
| x := x  -- [note] oh my goodness this is so convoluted!
def above : fmt → fmt → fmt
| f1 f2 := f1 ++ fmt.line ++ f2
def bracket : string → fmt → string → fmt
| l f r := group $ nest l.length $ l ++ f ++ r

end fmt

meta inductive pp_result : Type
| child : expr.address → expr → pp_result → pp_result
| append : pp_result → pp_result → pp_result
| of_format : format → pp_result
| nest : nat → pp_result → pp_result
| group : pp_result → pp_result

#check 234 + 5435
