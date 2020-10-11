example : true :=
begin
sorry #, -- broken
end

example : true := by { sorry # } -- broken

example : true := begin { sorry # } end -- broken

example : true := by trivial
#che