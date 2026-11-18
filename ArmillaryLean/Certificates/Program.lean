module

public import ArmillaryLean.Certificates.Exclusion

@[expose] public section

/-!
# Packed exclusion-tree programs

The words of an untrusted program are stored in a balanced tree. Each leaf
contains at most 42 twelve-bit words in one 512-bit-or-smaller natural number.
A complete parse supplies a typed exclusion tree to the verified checker.
-/

namespace ArmillaryLean.Exclusion

/-- A binary concatenation of packed twelve-bit words. -/
inductive Program where
  | chunk (count : Fin 43) (payload : Nat)
  | append (left right : Program)

/-- Unpack a fixed number of little-endian twelve-bit words. -/
def unpackWords : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, payload => (payload &&& 4095) :: unpackWords n (payload >>> 12)

/-- Decode the words in a packed program in order. -/
def Program.words : Program → List Nat
  | .chunk n p => unpackWords n p
  | .append left right => left.words ++ right.words

/-- Read exactly the requested number of row addresses. -/
def parseRows {Row : Type} (row : Nat → Option Row) :
    Nat → List Nat → Option (List Row × List Nat)
  | 0, rest => some ([], rest)
  | n + 1, address :: rest => do
      let r ← row address
      let (packed, suffix) ← parseRows row n rest
      return (r :: packed, suffix)
  | _ + 1, [] => none

/-- Parse one typed tree, with depth bounded by fuel, leaving the unused suffix. -/
def parseTree {Row Col : Type} [DecidableEq Row]
    (row : Nat → Option Row) (col : Nat → Option Col) :
    Nat → List Nat → Option (Tree Row Col × List Nat)
  | 0, _ => none
  | _ + 1, 0 :: address :: rest => do
      let r ← row address
      return (.closed r, rest)
  | _ + 1, 1 :: count :: rest => do
      let (packed, suffix) ← parseRows row count rest
      return (.packing packed, suffix)
  | fuel + 1, 2 :: address :: rest => do
      let c ← col address
      let (selected, afterSelected) ← parseTree row col fuel rest
      let (forbidden, afterForbidden) ← parseTree row col fuel afterSelected
      return (.split c selected forbidden, afterForbidden)
  | _ + 1, _ => none

/-- Check a packed program only when its complete contents parse as one tree. -/
def checkProgram {Row Col : Type} [DecidableEq Row] [DecidableEq Col]
    (rows : Rows Row Col) (row : Nat → Option Row) (col : Nat → Option Col)
    (budget depth : Nat) (anchor : Col) (program : Program) : Bool :=
  match parseTree row col depth program.words with
  | some (tree, []) => check rows budget {anchor} {anchor} tree
  | _ => false

/-- An accepted packed program rules out all small satisfying supports at its anchor. -/
theorem program_excludes {Row Col : Type} [DecidableEq Row] [DecidableEq Col]
    {rows : Rows Row Col} {row : Nat → Option Row} {col : Nat → Option Col}
    {budget depth : Nat} {anchor : Col} {program : Program} {support : Finset Col}
    (hcheck : checkProgram rows row col budget depth anchor program = true)
    (ha : anchor ∈ support) (hz : ZeroSyndrome rows support) (hw : support.card ≤ budget) : False := by
  unfold checkProgram at hcheck
  split at hcheck
  · exact anchor_excludes hcheck ha hz hw
  · contradiction

end ArmillaryLean.Exclusion
