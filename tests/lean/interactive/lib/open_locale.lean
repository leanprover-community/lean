open lean lean.parser interactive tactic native

@[user_command] meta def open_locale_cmd (_ : parse $ tk "open_locale") : parser unit :=
pure ()
