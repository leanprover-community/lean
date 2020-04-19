import widget

#eval html.cases (λ e, 0) (λ e, 1) (λ _ p c, 2) $ @html.of_string unit "hello"

#eval option.map html.element.tag $ @html.as_element unit $ html.div $ [html.of_string "hello"]
