open tactic

namespace tactic.interactive

meta def my_tac (p : interactive.parse lean.parser.itactic) : tactic unit :=
p

meta def my_tac_optional (p : interactive.parse (optional lean.parser.itactic)) : tactic unit :=
match p with
| some p := p
| none := tactic.trace "nothing"
end

meta def my_tac_raw (e : interactive.parse (lean.parser.reflect $ optional lean.parser.itactic)) : tactic unit :=
tactic.trace e

end tactic.interactive

meta def quote_tac : tactic unit := `[my_tac {tactic.trace "hi2"}]
meta def quote_tac_optional : tactic unit := `[my_tac_optional]
meta def quote_tac_raw : tactic unit := `[my_tac_raw {tactic.trace "hi2"}]

example : true := begin
    my_tac {tactic.trace "hi"},

    my_tac_optional {tactic.trace "hi"},
    my_tac_optional {},
    my_tac_optional,

    my_tac_raw {tactic.trace "hi"},
    my_tac_raw {},
    my_tac_raw,

    quote_tac,
    quote_tac_optional,
    quote_tac_raw,

    trivial
end
