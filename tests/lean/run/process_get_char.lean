import system.io

def data := "0123456789012345678901234567890"

meta def main := do
child ← io.proc.spawn {
    cmd := "echo",
    args := [data],
    stdout := io.process.stdio.piped
},
c1 <- io.fs.get_char child.stdout,
c2 <- io.fs.get_char child.stdout,
c3 <- io.fs.get_char child.stdout,
c4 <- io.fs.get_char child.stdout,
c5 <- io.fs.get_char child.stdout,
pure [c1, c2, c3, c4, c5]

#eval do
res ← tactic.unsafe_run_io main,
tactic.trace res,
guard $ res = data.to_list.take 5
