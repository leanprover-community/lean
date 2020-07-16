
import .eqn_api2

def foo_bar (a : Type) (x : a) : option a -> a
| none := x
| (some y) := y

def all : bool -> bool -> bool -> bool -> bool
| ff _  _  _  := ff
| _  ff _  _  := ff
| _  _  ff _  := ff
| _  _  _  ff := ff
| _  _  _  _  := tt

open tactic

meta def replace_internal_name (e : pexpr) : pexpr :=
expr.replace e $ λ e i,
match e with
| expr.const (name.mk_numeral _ _) ls := some $ expr.const `_ ls
| _ := none
end

run_cmd do
 e ← get_env,
 trace "foo",
 environment.defn_spec e ``foo >>= trace ∘ replace_internal_name,
 trace "foo_bar",
 environment.defn_spec e ``foo_bar >>= trace ∘ replace_internal_name,
 trace "all",
 environment.defn_spec e ``all >>= trace ∘ replace_internal_name,
 trace "f",
 environment.defn_spec e ``f >>= trace ∘ replace_internal_name,
 trace "g",
 environment.defn_spec e ``g >>= trace ∘ replace_internal_name,
 skip
