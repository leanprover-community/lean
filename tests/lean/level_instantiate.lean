#check level.instantiate

#eval level.to_string $ level.instantiate (level.param `x) [(`x, level.param `y)]

#eval level.to_string $ level.instantiate (level.param `x) [(`x, level.param `y), (`y, level.param `z)]

#eval level.to_string $ level.instantiate (level.param `x) [(`x, level.param `y), (`x, level.param `z)]

#eval level.to_string $ level.instantiate (level.max (level.param `x) (level.param `y)) [(`x, level.param `y), (`y, level.param `z)]
