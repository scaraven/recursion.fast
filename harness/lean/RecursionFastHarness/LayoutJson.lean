/-
# Harness: layout JSON → `Layout K`                                   (organiser harness code)

The badge path's indexer (`index`, `RecursionFastHarness/Driver.lean`) reads a layout as JSON
(schema `recursion.fast/layout/1`, `harness/README.md`): the submitted recursion layout `C_V` of a
claim, and the benchmark layout `L_chain(2^10)`. The challenge renderer turns the same file into
the Lean literal the certificate is about (`scripts/render-challenge.py`, `{{layout:C}}`). This
reader must produce the same layout as that literal, up to extensional equality of its functions
(so every computable `VK`/`IDX` gives the same key): it applies the renderer's checks (documented
keys only; every number a natural; every K element 16 lowercase hex digits; `|M| = t`,
`|S| = |c| = q`; matrix entries with `row < cons`, `col < 2·cols + 3`; `S` entries `< t`, never
wrapped), builds `add8` exactly as the renderer's closed form (`harness/render-layout.py`) and an
explicit table as `tabOf` does. CI cross-checks it against the renderer on `L_chain(16)` through
the contract's serialisation `Layout.words` (`probes/s6b/layout/ParseCheck.lean`). Duplicate keys
are rejected by the renderer (Lean's JSON parser keeps the last one); the harness only indexes
files the renderer accepted.
-/
import Lean.Data.Json
import RecursionFast.Contract

namespace RecursionFastHarness.LayoutJson
open Lean RecursionFast

/-- Parsing with an error message. -/
abbrev M := Except String

/-- A JSON natural number (an integer literal; no fraction, no exponent, not negative). -/
def nat (w : String) : Json → M ℕ
  | .num ⟨m, 0⟩ => if 0 ≤ m then pure m.toNat else throw s!"{w}: negative number"
  | j => throw s!"{w}: expected a natural number, got {j.compress.take 80}"

/-- A JSON natural number below `b`, as `Fin b` (out of range is an error, never a wrap). -/
def natBelow (w : String) (b : ℕ) (j : Json) : M (Fin b) := do
  let n ← nat w j
  if h : n < b then pure ⟨n, h⟩ else throw s!"{w}: {n} is not below {b}"

/-- The value of a lowercase hex digit. -/
def hexVal (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

/-- A K element: exactly 16 lowercase hex digits, the 64-bit word `K.bits`. -/
def kel (w : String) : Json → M K
  | .str s => do
    unless s.length = 16 do throw s!"{w}: not 16 hex digits: {s.take 40}"
    let mut n := 0
    for c in s.toList do
      match hexVal c with
      | some v => n := 16 * n + v
      | none => throw s!"{w}: not a lowercase hex digit in {s}"
    pure ⟨BitVec.ofNat 64 n⟩
  | j => throw s!"{w}: expected a K element (string), got {j.compress.take 80}"

/-- A JSON boolean. -/
def bool (w : String) : Json → M Bool
  | .bool b => pure b
  | j => throw s!"{w}: expected a boolean, got {j.compress.take 80}"

/-- A JSON array. -/
def arr (w : String) : Json → M (Array Json)
  | .arr a => pure a
  | j => throw s!"{w}: expected an array, got {j.compress.take 80}"

/-- A JSON object with exactly the keys `req` and possibly some of `opt`. -/
def obj (w : String) (req opt : List String) : Json → M (Std.TreeMap.Raw String Json compare)
  | .obj kvs => do
    for k in req do
      unless kvs.contains k do throw s!"{w}: missing key {k}"
    for (k, _) in kvs.toList do
      unless req.contains k || opt.contains k do throw s!"{w}: unknown key {k}"
    pure kvs
  | j => throw s!"{w}: expected an object, got {j.compress.take 80}"

/-- The value of a (checked) key. -/
def get (w : String) (o : Std.TreeMap.Raw String Json compare) (k : String) : M Json :=
  match o.get? k with
  | some v => pure v
  | none => throw s!"{w}: missing key {k}"

/-- The element of `K` with bits `n` (the renderer's `kx`). -/
def kx (n : ℕ) : K := ⟨BitVec.ofNat 64 n⟩

/-- The 8-bit add-with-carry table, the renderer's closed form `add8` verbatim. -/
def add8 : Table K := ⟨2 ^ 17, fun r c =>
  let x := r % 256
  let y := r / 256 % 256
  let ci := r / 65536
  let s := x + y + ci
  match c with
  | 0 => 1 | 1 => kx x | 2 => kx y | 3 => kx ci | 4 => kx (s % 256) | 5 => kx (s / 256) | _ => 0⟩

/-- An explicit table: its listed rows; cells outside them are `0` (the renderer's `tabOf`). -/
def tableOfRows (rows : Array (Array K)) : Table K :=
  ⟨rows.size, fun r c => (rows.getD r #[]).getD c 0⟩

/-- A fixed table: `null`, `{"kind": "add8"}` or `{"kind": "explicit", "rows": [[K]]}` (an
informational `"note"` is allowed). -/
def fixed (w : String) : Json → M (Option (Table K))
  | .null => pure none
  | j => do
    match j.getObjVal? "kind" with
    | .ok (.str "add8") => let _ ← obj w ["kind"] ["note"] j; pure (some add8)
    | .ok (.str "explicit") =>
      let o ← obj w ["kind", "rows"] ["note"] j
      let rows ← arr s!"{w}.rows" (← get w o "rows")
      let rows ← rows.mapIdxM fun r row => do
        (← arr s!"{w}.rows[{r}]" row).mapIdxM fun c v => kel s!"{w}.rows[{r}][{c}]" v
      pure (some (tableOfRows rows))
    | _ => throw s!"{w}: unknown fixed table {j.compress.take 80}"

/-- A gadget on views of width `cols + cols + 3`. -/
def gadget (w : String) (cols : ℕ) (j : Json) : M (Gadget K (cols + cols + 3)) := do
  let o ← obj w ["cons", "t", "q", "M", "S", "c"] ["names"] j
  let cons ← nat s!"{w}.cons" (← get w o "cons")
  let t ← nat s!"{w}.t" (← get w o "t")
  let q ← nat s!"{w}.q" (← get w o "q")
  let Ms ← arr s!"{w}.M" (← get w o "M")
  let Ss ← arr s!"{w}.S" (← get w o "S")
  let cs ← arr s!"{w}.c" (← get w o "c")
  unless Ms.size = t ∧ Ss.size = q ∧ cs.size = q do
    throw s!"{w}: |M| = {Ms.size}, |S| = {Ss.size}, |c| = {cs.size} for t = {t}, q = {q}"
  let Mv ← Ms.mapIdxM fun i m => do
    let es ← arr s!"{w}.M[{i}]" m
    es.toList.mapM fun e => do
      let we := s!"{w}.M[{i}][…]"
      match (← arr we e).toList with
      | [r, c, v] => pure (← natBelow s!"{we}.row" cons r, ← natBelow s!"{we}.col" (cols + cols + 3) c,
          ← kel s!"{we}.value" v)
      | _ => throw s!"{we}: expected [row, col, K]"
  let Sv ← Ss.mapIdxM fun i s => do
    (← arr s!"{w}.S[{i}]" s).toList.mapM (natBelow s!"{w}.S[{i}]" t)
  let cv ← cs.mapIdxM fun i v => kel s!"{w}.c[{i}]" v
  pure { cons, t, M := fun i => Mv.getD i.val [], q, S := fun i => Sv.getD i.val [],
         c := fun i => cv.getD i.val 0 }

/-- A port: bus, direction, selector column, message columns. -/
def port (w : String) (j : Json) : M Port := do
  let o ← obj w ["bus", "send", "sel", "msg"] [] j
  pure ⟨← nat s!"{w}.bus" (← get w o "bus"), ← bool s!"{w}.send" (← get w o "send"),
    ← nat s!"{w}.sel" (← get w o "sel"),
    (← (← arr s!"{w}.msg" (← get w o "msg")).toList.mapM (nat s!"{w}.msg"))⟩

/-- A chip. -/
def chip (w : String) (j : Json) : M (Chip K) := do
  let o ← obj w ["cols", "gadget", "ports", "fixed"] ["name", "colnames"] j
  let cols ← nat s!"{w}.cols" (← get w o "cols")
  pure { cols, gadget := ← gadget s!"{w}.gadget" cols (← get w o "gadget"),
         ports := ← (← arr s!"{w}.ports" (← get w o "ports")).toList.mapM (port s!"{w}.ports[…]"),
         fixed := ← fixed s!"{w}.fixed" (← get w o "fixed") }

/-- A bus kind. -/
def busKind (w : String) : Json → M BusKind
  | .str "sub" => pure .sub
  | .str "eq" => pure .eq
  | j => throw s!"{w}: expected \"sub\" or \"eq\", got {j.compress.take 80}"

/-- **A layout** from its JSON object: the chips in order, bus `b`'s kind the `b`-th listed one
(`eq` beyond the list, as the renderer's `List.getD`), the public chip. -/
def layout (j : Json) : M (Layout K) := do
  let o ← obj "layout" ["schema", "chips", "bus", "pub"] ["name", "params", "busnames"] j
  unless (← get "layout" o "schema") == Json.str "recursion.fast/layout/1" do
    throw "layout: schema must be \"recursion.fast/layout/1\""
  let chips ← (← arr "chips" (← get "layout" o "chips")).mapIdxM fun i c => chip s!"chips[{i}]" c
  let kinds ← (← arr "bus" (← get "layout" o "bus")).mapIdxM fun i b => busKind s!"bus[{i}]" b
  let pub ← nat "pub" (← get "layout" o "pub")
  pure ⟨chips.toList, fun b => kinds.getD b .eq, pub⟩

/-- A layout from JSON text. -/
def parse (s : String) : M (Layout K) := do
  layout (← Json.parse s)

end RecursionFastHarness.LayoutJson
