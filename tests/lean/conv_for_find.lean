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
