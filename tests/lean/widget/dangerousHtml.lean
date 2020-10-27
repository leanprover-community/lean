open widget

meta def danger : component tactic_state empty :=
component.pure (λ _,
  [h "div" [attr.val "dangerouslySetInnerHTML"
           $ json.object [("__html", "<div> hello this is some html. You can't inject script elements because they need to be <code>eval()</code>ed. </div>")]] []])

#html danger