-- see issue: https://github.com/leanprover-community/lean/issues/172

instance its_a_monad : monad option :=
{ pure := λ {_}, some
, bind := λ {α β} x f, option.rec_on x option.none f}

#eval @has_bind.bind option (@monad.to_has_bind _ its_a_monad) _ _ (some 4) some
