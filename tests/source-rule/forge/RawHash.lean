/-! S9 probe (source rule): Lean lexes `r#eval` as the identifier `r` followed by the command
`#eval` (`r#` opens a raw string only when the hashes are followed by `"`). `source-rule.py` treats
`r#` as a raw-string opener and, finding no closing `"#`, skips the rest of the file. Expected:
Lean prints the two lines below; `source-rule.py` reports 0 findings. -/
def r : Nat := 0
def foo : Nat := r#eval (IO.println "S9: #eval ran after r#" : IO Unit)
#eval (IO.println "S9: a second #eval, also invisible to the source rule" : IO Unit)
