namespace experiment
namespace nat
constant nat : Type.{1}
constant add : nat → nat → nat
constant le : nat → nat → Prop
constant one : nat
infixl (name := nat.add) `+` := add
infix (name := nat.le) `≤` := le
axiom add_assoc (a b c : nat) : (a + b) + c = a + (b + c)
axiom add_le_left {a b : nat} (H : a ≤ b) (c : nat) : c + a ≤ c + b
end nat

namespace int
constant int : Type.{1}
constant add : int → int → int
constant le : int → int → Prop
constant one1 : int
infixl (name := int.add) `+` := add
infix (name := int.le) `≤`  := le
axiom add_assoc (a b c : int) : (a + b) + c = a + (b + c)
axiom add_le_left {a b : int} (H : a ≤ b) (c : int) : c + a ≤ c + b
noncomputable definition lt (a b : int) := a + one1 ≤ b
infix (name := int.lt) `<`  := lt
end int
end experiment
