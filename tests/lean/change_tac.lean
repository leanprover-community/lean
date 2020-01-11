example : 1 + 2 = 3 :=
begin
  change 2 + 1 = 3,
  trace_state,
  refl
end

example : 1 + 2 = 3 :=
begin
  change 2 + 2 = 3 -- ERROR
end

example (h : 1 + 2 = 3) : 2 + 2 = 4 :=
begin
  change 2 + 1 = 3 at h,
  trace_state,
  refl
end

example (h : 1 + 2 = 3) : 2 + 2 = 4 :=
begin
  change 2 + 1 = 3 at h h, -- ERROR
end

example (h : 1 + 2 = 3) : 2 + 2 = 4 :=
begin
  change 2 + 1 = 3 at *, -- ERROR
end

example (h : 1 + 2 = 3) : 1 + 2 = 3 :=
begin
  change 1 + 2 with 2 + 1 at h,
  trace_state,
  refl
end

example (h : 1 + 2 = 1 + 2 + 1) : 1 + 2 = 3 :=
begin
  change 1 + 2 with 3 at *,
  trace_state,
  refl
end

example (h : 1 + 2 = 1 + 2 + 1) : 1 + 2 = 3 :=
begin
  change 1 + 2 with 4 at *, -- ERROR
end

example : true :=
begin
  have : ∀ x : ℕ, x = x,
  change ∀ y : ℕ, y = y,
  trace_state,
  admit,
  change ∀ y : ℕ, y = y at this,
  trace_state,
  trivial
end
