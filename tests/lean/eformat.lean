open tactic

meta def trace_tagged_debug : expr → tactic unit
| e := do
   tf ← tactic.pp_tagged e,
   f  ← tagged_format.m_untag (λ a f, do a ← pp a, pure $ "[" ++ a ++ ": " ++ f ++ "]") tf,
   tactic.trace f

meta def trace_tagged_debug_locals : tactic unit := do
  cs ← local_context,
  cs ← cs.mmap infer_type,
  cs.mmap' trace_tagged_debug

example (α : Type) (x : α) (h : 1 = 2) (f : ite ff true false) (g : x ≠ x) : true :=
begin
  trace_tagged_debug_locals,
  trivial
end

example (k : (-3 : int) < (1 + 1 : nat)) : true :=
begin
  trace_tagged_debug_locals, -- note the coe is present.
  trivial
end

example (k : Π {α β : Type}, α ≠ β) : true :=
begin
  trace_tagged_debug_locals,
  trivial
end

example (k : (λ α β : Type, α ≠ β) Prop Prop) : true :=
begin
  trace_tagged_debug_locals,
  trivial
end

example (S : set nat) (k : S = {3, 2, 1}) : true :=
begin
  trace_tagged_debug_locals,
  trivial
end
