#check `(true.intro)
#check (`(true.intro) : expr)

variables (h : true) [reflected h]
#check `(id h)
