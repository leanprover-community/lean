example (p q r : Prop) : p → (p ∧ q → r) → q → r :=
λ hp hpqr hq, hpqr (and.intro (id hp) hq)
            --^ "command":"info"

example (p q r : Prop) : p → (p ∧ q → r) → q → r :=
λ hp hpqr, by intro hq; exact hpqr (and.intro hp hq)
            --^ "command":"info"

example (p q r : Prop) : p → (p ∧ q → r) → q → r :=
λ hp hpqr, by intro hq; exact hpqr (and.intro hp hq)
                                  --^ "command":"info"

example (p q r : Prop) : p → (p ∧ q → r) → q → r :=
λ hp hpqr, by intro hq; exact hpqr (and.intro hp hq)
                    --^ "command":"info"

example (p q : Prop) : (p → p → q) → p → q :=
λ hppq, by intro hp; apply hppq hp; assumption
                        --^ "command":"info"