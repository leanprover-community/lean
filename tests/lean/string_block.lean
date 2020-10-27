#check /-" foo "-/
#check /-" /- foo -/ "-/
#check /-" /-"" foo -/ "-/
#check /-" /-"" foo -/ """-/
#check /-" /-"" foo -/ "-""""-/++""

#print /-"
## Markdown heading

String blocks are like comments:
```lean
/-- My declaration -/
def my_declaration : string :=
/-"
  They can be nicely nested
"-/
```

"-/