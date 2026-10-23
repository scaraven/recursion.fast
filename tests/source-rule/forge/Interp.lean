import RecursionFast.Contract
/-! S9 probe (source rule): a string literal inside an interpolation. Lean parses the interpolant
`"}"` as a term; `source-rule.py` closes the interpolation at the first `}` and from there on its
string/code parity is inverted, so the command on the next line is read as string content. Every
literal is terminated (the file ends with a comment holding one quote), so failing closed on
unterminated literals would not catch it. (Imports: the contract only, which every submission may import; the
S6b ForgeRaw body fits here the same way.) -/
def a : String := s!"{ "}" }"
run_cmd Lean.logInfo "S9: this command ran"
-- "
