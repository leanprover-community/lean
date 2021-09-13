prelude
import init.core

def A.a := 1
def B.b := 1
def C.c := 1
def foo.A.a := 2
def foo.B.b := 2
def foo.bar.A.a := 3

namespace foo
namespace bar

section open A B C
example : a = 3 := rfl
example : b = 2 := rfl
example : c = 1 := rfl
end

section open _root_.A
example : a = 1 := rfl
end

section open _root_.foo.A
example : a = 2 := rfl
end

end bar
end foo
