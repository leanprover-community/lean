example (a b : bool) : a = b := by cases a; cases b; simp
                                --^ "command": "info"
example (a b : bool) : a = b := by cases a; cases b; simp
                                         --^ "command": "info"
example (a b : bool) : a = b := by cases a; cases b; simp
                                                  --^ "command": "info"