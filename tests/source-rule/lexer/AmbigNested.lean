/- Fixture (never compiled): a string literal whose end depends on whether Lean reads it as
interpolated is rejected (fail closed), even where it is legitimate Lean. One per file: after it,
the lexer cannot know which reading Lean took. -/
def b : String := s!"value {s!"nested {1}"}"  -- REJECT
