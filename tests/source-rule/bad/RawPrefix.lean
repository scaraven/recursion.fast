/- Fixture (never compiled): `r` followed by `#` opens a raw string only when the hashes are
followed by a quote. -/
def r : Nat := 0
example : Nat := r#check r
def x := r##eval  -- REJECT
def y := r#"a raw string"# + r
