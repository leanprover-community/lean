prelude
import init.meta.expr
import init.meta.mk_dec_eq_instance
import init.meta.interactive

namespace expr

/-- An enum representing a recursive argument in an `expr` constructor (except the types of variables). -/
@[derive decidable_eq]
inductive coord : Type
| app_fn
| app_arg
| lam_var_type
| lam_body
| pi_var_type
| pi_body
| elet_var_type
| elet_assignment
| elet_body

namespace coord

def code: coord → ℕ
|coord.app_fn := 0 |coord.app_arg  := 1
|coord.lam_var_type := 2 |coord.lam_body := 3
|coord.pi_var_type := 4 |coord.pi_body := 5
|coord.elet_var_type := 6 |coord.elet_assignment := 7 |coord.elet_body := 8

-- [todo] there must be a way of doing this that doesn't suck
def repr: coord → string
|coord.app_fn := "app_fn" |coord.app_arg  := "app_arg"
|coord.lam_var_type := "lam_var_type" |coord.lam_body := "lam_body"
|coord.pi_var_type := "pi_var_type" |coord.pi_body := "pi_body"
|coord.elet_var_type := "elet_var_type" |coord.elet_assignment := "elet_assignment" |coord.elet_body := "elet_body"

instance : has_repr coord := ⟨repr⟩

instance has_lt : has_lt coord := ⟨λ x y, x.code < y.code⟩

instance dec_lt : decidable_rel ((<) : coord → coord → Prop) := by apply_instance

meta def follow : coord → expr → option expr
| (coord.app_fn)          (expr.app f a)         := some f
| (coord.app_arg)         (expr.app f a)         := some a
| (coord.lam_var_type)    (expr.lam  n bi y   b) := some y
| (coord.lam_body)        (expr.lam  n bi y   b) := some b
| (coord.pi_var_type)     (expr.pi   n bi y   b) := some y
| (coord.pi_body)         (expr.pi   n bi y   b) := some b
| (coord.elet_var_type)   (expr.elet n    y a b) := some y
| (coord.elet_assignment) (expr.elet n    y a b) := some a
| (coord.elet_body)       (expr.elet n    y a b) := some b
| _                       _                      := none

end coord

/-- An address is a list of coordinates used to reference subterms of an expression.
The topmost coordinate in the list corresponds to the start of the expression. -/
def address : Type := list coord

namespace address

-- [todo] this should be a total ordering on addresses?
instance has_lt : has_lt address := show has_lt (list coord), by apply_instance

instance dec_lt : decidable_rel ((<) : address → address → Prop) := by apply_instance

protected def to_string : address → string := λ a, to_string $ list.map coord.repr a

instance has_repr : has_repr address := ⟨address.to_string⟩
instance has_to_string : has_to_string address := ⟨address.to_string⟩

instance has_append : has_append address := ⟨list.append⟩


/-- `as_below x y` is some z when it finds `∃ z, x = y ++ z` -/
def as_below : address → address → option address
|a [] := some a -- [] ++ a = a
|[] _ := none   -- (h::t) ++ _ ≠ []
|(h₁ :: t₁) (h₂ :: t₂) := if h₁ = h₂ then as_below t₁ t₂ else none -- if t₂ ++ z = t₁ then (h₁ :: t₁) ++ z = (h₁ :: t₂)

def is_below : address → address → bool | a₁ a₂ := option.is_some $ as_below a₁ a₂

infixr  ` ≺ `:50 := is_below

meta def follow : address → expr → option expr
| [] e := e
| (h::t) e := coord.follow h e >>= follow t

end address

end expr
