local attribute [pp_numeral_type] fin

#check (17 : fin 22)

local attribute [pp_numeral_type] nat

#check (17 : fin 22)
#check nat.zero.succ.succ.succ

set_option pp.numeral_types true

#check 2 + 1 = 3

#check (17 : fin 22)

#check 3

#check nat.zero.succ.succ.succ

set_option pp.all true

#check 3

#check nat.zero.succ.succ.succ

set_option pp.all false
set_option pp.nat_numerals false
set_option pp.numeral_types false
local attribute [-pp_numeral_type] nat

#check 3

#check nat.zero.succ.succ.succ
