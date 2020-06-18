@[hole_command] meta def foo : hole_command :=
{ name := "a b", descr := "foobarbaz", action := λ _, failure }

--^ "command": "all_hole_commands"

def x : nat → nat :=
λ a, {! a + a !}
     --^ "command": "hole", "action": "a b"
