meta def list.async_map {α β} (f : α → β) (xs : list α) : list β :=
(xs.map (λ x, task.delay $ λ _, f x)).map task.get

#eval ((list.range 1000000).async_map (+1)).foldl (+) 0