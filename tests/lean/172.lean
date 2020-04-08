-- issue: https://github.com/leanprover-community/lean/issues/172

instance its_a_monad : monad option :=
{ pure := λ _, some
, bind := λ α β x f, option.rec_on x option.none f}

#eval @has_bind.bind option (@monad.to_has_bind _ its_a_monad) _ _ (some 4) some

-- issue: https://github.com/leanprover-community/lean/issues/111

universes u

inductive Incr (a : Type u) : Type u
| Z : Incr
| S : a -> Incr

instance incr_functor : functor Incr :=
  { map := λ α β f a, Incr.rec_on a (Incr.Z) (Incr.S ∘ f) }

instance incr_has_bind : has_bind Incr :=
  { bind := λ _ _ a f, Incr.rec_on a (Incr.Z) f }

instance incr_has_seq : has_seq Incr :=
  { seq := λ _ _ x y, Incr.rec_on x (Incr.Z) (λ f, f <$> y) }

instance incr_has_pure : has_pure Incr :=
  { pure := λ _, Incr.S }

instance incr_applicative : applicative Incr := {}

instance incr_monad_real : monad Incr := {} -- segfaults on old versions.

instance {α : Type u} [has_repr α] : has_repr (Incr α) :=
⟨λ x, Incr.cases_on x "Z" (λ a, "(S " ++ repr a ++ ")")⟩

#eval Incr.S 4 >>= Incr.S