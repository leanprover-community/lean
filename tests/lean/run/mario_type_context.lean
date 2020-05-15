-- see https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/witt.20vectors/near/168407094
set_option profiler true
open tactic

constant semiring : Type → Type
constant comm_semiring : Type → Type
constant ring : Type → Type
constant comm_ring : Type → Type

attribute [class] semiring comm_semiring ring comm_ring

constant comm_ring.to_comm_semiring {α : Type} [comm_ring α] : comm_semiring α
constant comm_semiring.to_semiring {α : Type} [comm_semiring α] : semiring α

attribute [instance] comm_ring.to_comm_semiring comm_semiring.to_semiring

def bar (α) [semiring α] : α := sorry

lemma foo (α) [comm_ring α]
  (h : bar α = @bar α (@comm_semiring.to_semiring α _)) : true :=
by do
  h ← get_local `h,
  ht ← infer_type h,
  `(%%h1 = %%h2) ← return ht,
  ht' ← to_expr ``(%%h2 = %%h2),
  pr ← mk_app `eq.refl [ht],
  pr' ← mk_app `eq.refl [ht'],
  trace [ht, ht, pr', h],
  try_for 100 $ mk_mapp `eq.mp [ht, ht, pr', h], -- slow step
  admit
