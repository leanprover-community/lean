example (xs : list ℕ) : ℕ :=
begin
  induction xs,
  case list.cons {}
end

example (xs : list ℕ) : ℕ :=
begin
  cases xs,
  case list.cons {}
end

example (xs : list ℕ) : ℕ :=
begin
  induction xs,
  case list.cons : x xs {
    cases xs,
    case list.cons : x xs {}
  }
end

open list
example (xs : list ℕ) : ℕ :=
begin
  induction xs,
  case cons {}
end

example (xs : list ℕ) : ℕ :=
begin
  cases h : xs,
  case list.cons : y ys {},
end

example (xs : list ℕ) : ℕ :=
begin
  cases xs,
  case no_such_case {}
end

example (xs : list ℕ) : ℕ :=
begin
  cases xs,
  case list.cons {}
end

example (xs ys : list ℕ) : ℕ :=
begin
  cases xs; cases ys,
  case cons {}
end

example (xs : list ℕ) : ℕ :=
begin
  cases xs,
  case cons : x xs too_many_names {}
end

example (xs ys : list ℕ) : ℕ :=
begin
  induction xs; induction ys,
  case cons cons : x xs ih too_many_names {}
end

example (xs ys : list ℕ) : ℕ :=
begin
  with_cases { induction xs; induction ys },
  case cons cons : x xs ih_xs y ys ih_ys {},
end

example (xs : list ℕ) : ℕ :=
begin
  induction xs,
  case list.cons : x xs ih { apply ih },
  case list.nil { apply 0 }
end

example (xs : list ℕ) : ℕ :=
begin
  cases xs,
  case nil { exact 0 },
  case cons : x xs { exact 0 }
end
