#check `(true.intro)
#check (`(true.intro) : expr)

variables (h : true) [reflected _ h]
#check `(id h)
