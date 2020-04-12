open lean lean.parser interactive tactic

@[user_command]
meta def open_locale_cmd (_ : parse $ tk "open_locale") : parser unit :=
ident *> pure ()
