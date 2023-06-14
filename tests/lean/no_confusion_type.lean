namespace Ex
open nat

inductive vector (A : Type) : nat → Type
| vnil  : vector nat.zero
| vcons : Π {n : nat}, A → vector n → vector (succ n)

#check vector.no_confusion_type
constants a1 a2 : nat
constants v1 v2 : vector nat 2
constant  P     : Type
#reduce vector.no_confusion_type P (vector.vcons a1 v1) (vector.vcons a2 v2)
end Ex

namespace ExSemiReducible
open nat

def wrapped_nat (n : nat) := nat

structure with_wrapped : Type :=
(n : nat)
(m : wrapped_nat n)

#check with_wrapped.no_confusion_type
constants (P : Type) (n1 n2 : nat) (m1 : wrapped_nat n1) (m2 : wrapped_nat n2)
#reduce with_wrapped.no_confusion_type P (with_wrapped.mk _ m1) (with_wrapped.mk _ m2)

end ExSemiReducible
