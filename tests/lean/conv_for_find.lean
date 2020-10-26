-- typos should be caught
example {a b c : ℕ} : (a * b) * c = (a * b) * c := begin
  conv {
    rw does_not_exist,
  },
end

example {a b c : ℕ} : (a * b) * c = (a * b) * c := begin
  conv {
    for (_ * _) [1] {
      rw does_not_exist,
    },
  },
end

example {a b c : ℕ} : (a * b) * c = (a * b) * c := begin
  conv {
    find (_ * _) {
      rw does_not_exist,
    },
  },
end

-- filled in metavariables should remain filled
example {a b : ℕ} : ∃ x, x * a = a * x :=  begin
  existsi _,
  conv {
    rw nat.mul_comm b a,
  },
end

-- but this unfortunately doesn't work for `find` and `for`
example {a b : ℕ} : ∃ x, x * a = a * x :=  begin
  existsi _,
  conv {
    find (_ * _) {
      rw nat.mul_comm b a,
    },
  },
end

example {a b : ℕ} : ∃ x, x * a = a * x :=  begin
  existsi _,
  conv {
    for (_ * _) [1] {
      rw nat.mul_comm b a,
    },
  },
end

-- matching should work under binders
example {ι} (p : ι → Prop) : (∀ i, p i) ↔ (∀ j, p j) :=
begin
  conv {
    find (p _) {
      trace_lhs,
    },
  },
end

example {ι} (p : ι → Prop) : (∀ i, p i) ↔ (∀ j, p j) :=
begin
  conv {
    for (p _) [1, 2] {
      trace_lhs,
    },
  },
end
