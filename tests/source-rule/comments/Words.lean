/- Fixture (never compiled): rejected words in comments and strings only. The lexer (net 1) skips
them; the raw scan (net 2) reports each such line, by design. -/
-- run_meta in a line comment  -- REJECT
/- #eval in a block comment -/  -- REJECT
/-- a docstring that mentions unsafeCast -/  -- REJECT
def a := "a string with persistentEnvExtensionsRef"  -- REJECT
def b := r#"raw: initialize"#  -- REJECT
def c := 0 -- partial  -- REJECT
def d := 'x' -- a comment that says: open Lean  -- REJECT
