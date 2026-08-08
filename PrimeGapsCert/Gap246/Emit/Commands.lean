/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import PrimeGapsCert.Gap246.Emit.SourceGen
public import PrimeGapsCert.Gap246.Emit.State
public meta import PrimeGapsCert.Gap246.Emit.State
public meta import PrimeGapsCert.Gap246.Kernel.Moments

import PrimeGapsCert.Gap246.Kernel.Extra
import PrimeGapsCert.Gap246.Kernel.Moments

/-! # Raw theorem emission for the packed moment certificate -/

@[expose] public section

namespace cert246Data.Emit

open Lean

/-- Namespace receiving generated data and theorem declarations. -/
meta def realNamespace : Name := `cert246Data

/-- `Eq Bool lhs rhs` as a raw expression. -/
meta def eqBool (lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) lhs rhs

/-- Register an opaque natural definition. -/
meta def addNatDef (name : Name) (value : ℕ) : CoreM Unit := do
  addDecl (forceExpose := true) (.defnDecl {
    name, levelParams := [], type := mkConst ``Nat, value := mkNatLit value
    hints := .opaque, safety := .safe
  })
  addDocStringCore name "Generated packed certificate datum."

/-- Register a reducible natural definition for a value consumed by a higher-order check. -/
meta def addNatAbbrev (name : Name) (value : ℕ) : CoreM Unit := do
  addDecl (forceExpose := true) (.defnDecl {
    name, levelParams := [], type := mkConst ``Nat, value := mkNatLit value
    hints := .abbrev, safety := .safe
  })
  addDocStringCore name "Generated packed certificate datum."

/-- Expression for `Lean.RArray ℕ`. -/
meta def rarrayNat : Expr := mkApp (mkConst ``Lean.RArray [.zero]) (mkConst ``Nat)

/-- Encode a packed-leaf tree as an expression. -/
meta partial def treeExpr : Lean.RArray ℕ → Expr
  | .leaf value =>
      mkApp2 (mkConst ``Lean.RArray.leaf [.zero]) (mkConst ``Nat) (mkNatLit value)
  | .branch pivot left right =>
      mkApp4 (mkConst ``Lean.RArray.branch [.zero]) (mkConst ``Nat) (mkNatLit pivot)
        (treeExpr left) (treeExpr right)

/-- Encode a balanced tree whose leaves are references to existing expressions. -/
meta partial def referenceTreeExpr (type : Expr) : Lean.RArray Expr → Expr
  | .leaf value =>
      mkApp2 (mkConst ``Lean.RArray.leaf [.zero]) type value
  | .branch pivot left right =>
      mkApp4 (mkConst ``Lean.RArray.branch [.zero]) type (mkNatLit pivot)
        (referenceTreeExpr type left) (referenceTreeExpr type right)

/-- Register a packed-leaf tree from its already independent leaves. -/
meta def addTreeDef (name : Name) (leaves : Array ℕ) : CoreM Unit := do
  if h : 0 < leaves.size then
    addDecl (forceExpose := true) (.defnDecl {
      name, levelParams := [], type := rarrayNat
      value := treeExpr (Lean.RArray.ofArray leaves h)
      hints := .opaque, safety := .safe
    })
    addDocStringCore name "Generated packed certificate table."
  else
    throwError "cert246Data: empty tree {name}"

/-- Register a reducible outer tree whose leaves reference separately stored trees. -/
meta def addTreeReferenceAbbrev (name : Name) (leaves : Array Expr) : CoreM Unit := do
  if h : 0 < leaves.size then
    let valueType := rarrayNat
    let type := mkApp (mkConst ``Lean.RArray [.zero]) valueType
    addDecl (forceExpose := true) (.defnDecl {
      name, levelParams := [], type
      value := referenceTreeExpr valueType (Lean.RArray.ofArray leaves h)
      hints := .abbrev, safety := .safe
    })
    addDocStringCore name "Generated packed certificate table."
  else
    throwError "cert246Data: empty referenced tree {name}"

/-- Register a reducible packed tree for a value consumed by a higher-order check. -/
meta def addTreeAbbrev (name : Name) (leaves : Array ℕ) : CoreM Unit := do
  if h : 0 < leaves.size then
    addDecl (forceExpose := true) (.defnDecl {
      name, levelParams := [], type := rarrayNat
      value := treeExpr (Lean.RArray.ofArray leaves h)
      hints := .abbrev, safety := .safe
    })
    addDocStringCore name "Generated packed certificate table."
  else
    throwError "cert246Data: empty tree {name}"

/-- Register a boolean theorem proved by kernel reduction of reflexivity. -/
meta def addBoolThm (name : Name) (type : Expr) : CoreM Unit := do
  addDecl (forceExpose := true)
    (.thmDecl { name, levelParams := [], type, value := reflBoolTrue })

/-- Generated constant expression. -/
meta def tableExpr (ns : Name) (name : String) : Expr :=
  mkConst (ns ++ Name.mkSimple name)

/-- Geometry literals for a fixed-width packed tree. -/
meta def treeLiterals (width : ℕ) : Array Expr :=
  let shift := Gen.chunkShift width
  #[mkNatLit shift, mkNatLit ((1 <<< shift) - 1), mkNatLit width,
    mkNatLit ((1 <<< width) - 1)]

/-- Geometry literals for a fixed-width packed tree regrouped four leaves to one. -/
meta def leafTreeLiterals (width : ℕ) : Array Expr :=
  let shift := Gen.levelChunkShift width
  #[mkNatLit shift, mkNatLit ((1 <<< shift) - 1), mkNatLit width,
    mkNatLit ((1 <<< width) - 1)]

/-- Row blocks of approximately `target` triangular entries. -/
meta def rowBlocks (signatureCount target : ℕ) : Array (ℕ × ℕ × ℕ) := Id.run do
  let mut blocks := #[]
  let mut lo := 0
  let mut index := 0
  let mut index0 := 0
  let mut count := 0
  let mut row := 0
  while row < signatureCount do
    count := count + row + 1
    index := index + row + 1
    row := row + 1
    if count ≥ target ∨ row = signatureCount then
      blocks := blocks.push (lo, row, index0)
      lo := row
      index0 := index
      count := 0
  return blocks

/-- Measured theorem-size target for one emitted row block. -/
meta def blockEntries : ℕ := 96

/-- Bounds of one slice of a balanced partition, extra elements assigned to the front. -/
meta def sliceRange (total slices slice : ℕ) : ℕ × ℕ :=
  let size := total / slices
  let extra := total % slices
  let lo := slice * size + min slice extra
  (lo, lo + size + if slice < extra then 1 else 0)

/-- Raw type of the signature/erase-structure check. -/
meta def dataType (ns : Name) (dims : Gen.SharedDims) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Kernel.dataCheck)
    #[mkNatLit dims.signatureCount, mkNatLit dims.labelCount, mkNatLit dims.maxCount,
      mkNatLit dims.degreeBound, tableExpr ns "sigEnc", tableExpr ns "eraseEnc",
      tableExpr ns "labelEnc"])
    (mkConst ``Bool.true)

/-- Raw type of the factorial-table check. -/
meta def factorialType (ns : Name) (dims : Gen.SharedDims) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Kernel.factCheck)
    #[mkNatLit ((1 <<< Gen.factorialWidth) - 1), mkNatLit dims.factorialCount,
      tableExpr ns "factT"])
    (mkConst ``Bool.true)

/-- Raw type of the signature-size and part-bound check. -/
meta def encodingType (ns : Name) (dims : Gen.SharedDims) : Expr :=
  let partBound := (dims.factorialCount - 1) / 4
  eqBool (mkAppN (mkConst ``cert246Kernel.encCheck)
    #[mkNatLit dims.signatureCount, mkNatLit dims.maxCount, mkNatLit partBound,
      tableExpr ns "sigEnc"])
    (mkConst ``Bool.true)

/-- Raw type of the packed erase-target lookup check. -/
meta def eraseTargetType (ns : Name) (dims : Gen.SharedDims) : Expr :=
  let geometry := treeLiterals Gen.indexWidth
  eqBool (mkAppN (mkConst ``cert246Data.eraseTargetCheck)
    #[mkNatLit dims.signatureCount, mkNatLit dims.degreeBound, geometry[0]!, geometry[1]!,
      tableExpr ns "sigEnc", tableExpr ns "eraseTargetT"])
    (mkConst ``Bool.true)

/-- Check the shared packed inputs after importing the separate validation kernel. -/
elab "cert246Data_emit_shared_checks" : command =>
  Elab.Command.liftCoreM do
    let dims ← readSharedDims
    addBoolThm (realNamespace ++ `data_ok) (dataType realNamespace dims)
    addBoolThm (realNamespace ++ `fact_ok) (factorialType realNamespace dims)
    addBoolThm (realNamespace ++ `enc_ok) (encodingType realNamespace dims)
    addBoolThm (realNamespace ++ `erase_target_ok) (eraseTargetType realNamespace dims)

attribute [nolint defsWithUnderscore] commandCert246Data_emit_shared_checks

end cert246Data.Emit
