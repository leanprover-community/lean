
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

run_cmd do
 e ← get_env,
 trace "foo",
 environment.defn_spec e ``foo >>= trace,
 trace "foo_bar",
 environment.defn_spec e ``foo_bar >>= trace,
 trace "all",
 environment.defn_spec e ``all >>= trace,
 trace "f",
 environment.defn_spec e ``f >>= trace,
 trace "g",
 environment.defn_spec e ``g >>= trace,
 skip
