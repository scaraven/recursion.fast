/- Fixture for scripts/source-rule.py (never compiled): every line marked `-- REJECT` must be
reported, and no other line. One rejected form per line. -/
import Lean.Elab  -- REJECT
import Lake  -- REJECT
import Qq  -- REJECT
open Lean Meta in  -- REJECT
open Nat Qq  -- REJECT
open _root_.Lean.Elab  -- REJECT
run_meta pure ()  -- REJECT
run_cmd pure ()  -- REJECT
run_elab pure ()  -- REJECT
example : True := by run_tac pure ()  -- REJECT
example : True := by run_tacq pure ()  -- REJECT
example : True := by conv => run_conv pure ()  -- REJECT
def a : Nat := by_elab pure (Lean.mkNatLit 1)  -- REJECT
def b : Nat := by_elabq pure q(1)  -- REJECT
def c : Nat := eval% 1 + 1  -- REJECT
#eval 1  -- REJECT
#eval! 1  -- REJECT
#exit  -- REJECT
#guard 1 = 1  -- REJECT
#test ∀ n : Nat, n = n  -- REJECT
#synth Inhabited Nat  -- REJECT
elab "x" : term => pure (Lean.mkNatLit 1)  -- REJECT
elab_rules : term | `(x) => pure default  -- REJECT
macro "y" : term => `(1)  -- REJECT
macro_rules | `(y) => `(2)  -- REJECT
syntax "z" : term  -- REJECT
declare_syntax_cat foo  -- REJECT
initialize r : IO.Ref Nat ← IO.mkRef 0  -- REJECT
builtin_initialize pure ()  -- REJECT
register_simp_attr foo  -- REJECT
register_option foo : Bool := {defValue := false}  -- REJECT
unsafe def u : Nat := 0  -- REJECT
partial def p : Nat → Nat := p  -- REJECT
def v : Nat := unsafeCast 0  -- REJECT
def w := unsafeBaseIO (pure 0)  -- REJECT
def w2 := ptrAddrUnsafe 0  -- REJECT
def x := Lean.persistentEnvExtensionsRef  -- REJECT
def x2 := «persistentEnvExtensionsRef»  -- REJECT
def x3 := Lean.«envExtensionsRef».get  -- REJECT
@[implemented_by u] def i : Nat := 0  -- REJECT
@[extern "f"] opaque e : Nat  -- REJECT
@[cpass] def cp := 0  -- REJECT
structure S where n : Nat with @[computed_field] m : S → Nat  -- REJECT
set_option compiler.extract_closed false in  -- REJECT
set_option debug.skipKernelTC true  -- REJECT
set_option interpreter.prefer_native true  -- REJECT
set_option trace.compiler.ir.result true  -- REJECT
simproc foo (x) := fun _ => pure .continue  -- REJECT
dsimproc foo2 (x) := fun _ => pure .continue  -- REJECT
simproc_decl foo3 (x) := fun _ => pure .continue  -- REJECT
def s1 := s!"a {unsafeCast 0} b"  -- REJECT
def s2 := s!"a {1} {
  unsafeCast 0} b"  -- REJECT
example : True := by test_extern Nat.add 1 2  -- REJECT
compile_inductive% Foo  -- REJECT
def cd := compile_def% Foo.bar  -- REJECT
sudo set_option maxRecDepth 1 in  -- REJECT
def lp := leading_parser "evil"  -- REJECT
def tp := trailing_parser "evil"  -- REJECT
set_library_suggestions fun _ _ => pure #[]  -- REJECT
@[library_suggestions] def sel := 0  -- REJECT
@[command_parser] def cp' := 0  -- REJECT
@[term_elab foo] def te := 0  -- REJECT
@[command_elab foo] def ce := 0  -- REJECT
@[simp, tactic foo] def ta := 0  -- REJECT
@[local init foo] def ini := 0  -- REJECT
@[export lean_foo] def ex := 0  -- REJECT
@[delab app.foo] def de := 0  -- REJECT
@[app_unexpander foo] def ue := 0  -- REJECT
attribute [csimp] foo_eq  -- REJECT
grind_propagator ↓foo (e) := pure ()  -- REJECT
declare_config_elab elabFoo Foo  -- REJECT
register_label_attr foo  -- REJECT
builtin_simproc foo (x) := fun _ => pure .continue  -- REJECT
elab_stx_quot Foo.quot  -- REJECT
def dbg := do idbg 0; pure ()  -- REJECT
#time theorem tt : True := trivial  -- REJECT
def eq := 1 == 1 -- eval with no % is a name: fine, but the next line is not
def e2 := eval % 2  -- REJECT
