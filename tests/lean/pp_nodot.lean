def foo := ℕ
def foo.x : foo → foo := nat.succ

variables (y : foo)

#check y.x -- uses dot notation

section
local attribute [pp_nodot] foo.x
#check y.x -- doesn't use dot notation
end

section
set_option pp.all true
#check y.x -- doesn't use dot notation
end