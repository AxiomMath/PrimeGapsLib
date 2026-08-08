/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
# The `pg_tag` attribute

This module provides the `@[pg_tag "<paper>" "<tag>"]` attribute used to mark
Lean declarations that formalize a specific blueprint entity from one of the
prime gaps source papers.

The attribute is the prime-gaps analogue of Mathlib's `@[stacks TAG]` (see
`Mathlib.Tactic.StacksAttribute`), adapted to the bounded-gaps blueprint.

## Usage

```
@[pg_tag "bg246" "def_S1"]
noncomputable def S₁ {k : ℕ} (h : Fin k → ℕ) (l : (Fin k → ℕ) → ℝ)
    (N : ℕ) (w₀ : ZMod (W N)) : ℝ :=
  ∑ n ∈ Ioc N (2 * N) with (n : ℕ) = w₀, weight h l n
```

Applying the attribute:
* registers `(declName, paperSlug, tag)` to the environment via the `pgTagExt`
  persistent extension;
* appends a docstring suffix `Maynard tag def_S1` so doc-gen output links back to the blueprint.

## Contents

* `PrimeGaps.PaperTag.Tag` — environment-extension entry.
* `PrimeGaps.PaperTag.pgTagExt` — the persistent environment extension.
* `PrimeGaps.PaperTag.addPgTagEntry` — register a single entry.
* `@[pg_tag …]` — the user-facing attribute.
* `#pg_tags` — list every registered tag in the current environment.

-/

public meta section

open Lean Elab

namespace PrimeGaps.PaperTag

/-- A single `pg_tag` entry: the tagged declaration name, the paper slug
(`maynard`), the paper-internal tag (the sanitized LaTeX label, e.g.
`def-simplex`), and an optional comment supplied with the attribute. -/
structure Tag where
  /-- The name of the declaration carrying this `pg_tag`. -/
  declName : Name
  /-- The slug of the source paper (currently always `"maynard"`). -/
  paper : String
  /-- The paper-internal tag identifier — a sanitized LaTeX label such
  as `"def-simplex"` or `"lem-lambda-from-y"`. -/
  tag : String
  /-- An optional comment supplied with the attribute. Empty when omitted.
  Mirrors the `comment` field of Mathlib's `CrossRef.Tag`. -/
  comment : String :=""
  deriving BEq, Hashable

/-- Persistent environment extension storing every `pg_tag` entry visible to
the current build. Modelled directly on `Mathlib.StacksTag.tagExt`. -/
initialize pgTagExt : SimplePersistentEnvExtension Tag (Array (Array Tag)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn tags := tags
    addEntryFn tags _ := tags
  }

/-- Register `(declName, paper, tag, comment)` with `pgTagExt`. -/
def addPgTagEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (paper tag : String) (comment : String := "") : m Unit :=
  modifyEnv (pgTagExt.addEntry · { declName, paper, tag, comment })

/-- The `pg_tag` attribute. Use as `@[pg_tag "<paper-slug>" "<tag>"]`
or `@[pg_tag "<paper-slug>" "<tag>" "<comment>"]`, e.g.

```
@[pg_tag "bg246" "def_S1"]
noncomputable def S₁ {k : ℕ} (h : Fin k → ℕ) (l : (Fin k → ℕ) → ℝ)
    (N : ℕ) (w₀ : ZMod (W N)) : ℝ :=
  ∑ n ∈ Ioc N (2 * N) with (n : ℕ) = w₀, weight h l n

@[pg_tag "bg246" "lem_foo" "the squarefree case"]
theorem PrimeGaps.foo : … := …
```

The first two arguments are mandatory; the third (comment) is optional.
All must be string literals. The tag is the LaTeX label (`def_foo`).
The optional comment is stored in the `Tag` extension entry and shown by `#pg_tags`,
mirroring Mathlib's `@[stacks TAG "comment"]`.
-/
syntax (name := pgTag) "pg_tag" ppSpace str ppSpace str (ppSpace str)? : attr

private def blueprintURL (paper tag : String) : String := s!"todo {paper} {tag}"

private def humanPaperLabel (paper : String) : String :=
  match paper with
  | "bg246" =>"Lean formalization of bounded gaps between primes"
  | s => s

initialize Lean.registerBuiltinAttribute {
  name := `pgTag
  descr :="Mark a Lean decl as formalizing a prime-gaps blueprint entity."
  add := fun decl stx _attrKind ↦ do
    let (paper, tag, comment) ← match stx with
      | `(attr| pg_tag $paper:str $tag:str $[$comment:str]?) =>
        pure (paper.getString, tag.getString, (comment.map (·.getString)).getD "")
      | _ => throwUnsupportedSyntax
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let url := blueprintURL paper tag
    let label := humanPaperLabel paper
    let commentInDoc := if comment = "" then "" else s!" ({comment})"
    let line := s!"[{label} tag {tag}]({url}){commentInDoc}"
    let newDoc := [oldDoc, line]
    addDocStringCore decl <| "\n\n".intercalate (newDoc.filter (· != ""))
    addPgTagEntry decl paper tag comment
  -- Matches Mathlib's `@[stacks]`: must fire before elaboration so the
  -- docstring is set while it is still mutable.
  applicationTime := .beforeElaboration
}

/-- Add a `pg_tag` to an upstream (Mathlib) declaration without modifying
its source file. Usage:

```
add_to_pg "maynard" "def_mobius" "optional comment" ArithmeticFunction.moebius
```

The comment string is optional. The behaviour matches `@[pg_tag …]`: the
`(declName, paper, tag)` triple is registered with `pgTagExt`.

This is the bounded-gaps analogue of Mathlib's `add_to_stacks` command (see
`Stacks/Tactic/StacksAttribute.lean` in the Stacks project). Use it to
pair a blueprint entity with a Mathlib decl that already proves the
content, without writing a wrapper in the bounded-gaps tree. -/
syntax (name := addToPg)
  "add_to_pg" ppSpace str ppSpace str (ppSpace str)? ppSpace ident : command

/-- Elaborator for the `add_to_pg` command. -/
@[command_elab addToPg]
def addToPgElab : Lean.Elab.Command.CommandElab :=
  fun stx ↦ match stx with
  | `(command| add_to_pg $paper:str $tag:str $[$comment:str]? $declStx:ident) => do
    let paperStr := paper.getString
    let tagStr := tag.getString
    let commentStr := (comment.map (·.getString)).getD ""
    let declList ← Lean.Elab.Command.liftCoreM <| Lean.resolveGlobalConst declStx
    let [decl] := declList
      | throwError m!"Ambiguous identifier: {declList}"
    Lean.Elab.Command.runTermElabM fun _ ↦ do
      Lean.Elab.Term.addTermInfo' declStx (← Lean.Meta.mkConstWithFreshMVarLevels decl)
    -- Warn if this declaration already carries this `pg_tag`, mirroring
    -- the `add_to_stacks` duplicate detection. The duplicate entry is
    -- still recorded (matching `add_to_stacks`); the warning surfaces the
    -- redundancy so the user can drop one of the two annotations.
    let env ← Lean.Elab.Command.liftCoreM Lean.getEnv
    let state := Lean.PersistentEnvExtension.getState pgTagExt env
    let existing := state.2.flatten.toList ++ state.1
    if existing.any fun t ↦ t.declName == decl && t.paper == paperStr && t.tag == tagStr then
      Lean.logWarningAt stx
        m!"'{decl}' already has the pg_tag {paperStr}/{tagStr}; skipping duplicate."
    Lean.Elab.Command.liftCoreM <| addPgTagEntry decl paperStr tagStr commentStr
  | _ => throwUnsupportedSyntax

end PrimeGaps.PaperTag

namespace PrimeGaps.PaperTag

/-- `#pg_tags` lists every declaration carrying a `@[pg_tag …]` attribute in
the current environment. -/
elab (name := pgTagsCmd) "#pg_tags" : command => do
  let env ← Command.liftCoreM getEnv
  let entries := PersistentEnvExtension.getState PrimeGaps.PaperTag.pgTagExt env
  let entries := entries.2.flatten.appendList entries.1
    |>.qsort (fun a b ↦ a.paper < b.paper || (a.paper = b.paper && a.tag < b.tag))
  if entries.isEmpty then
    logInfo "No pg_tags found."
  else
    let mut msgs := #[m!""]
    for d in entries do
      let cmt := if d.comment = "" then "" else s!" ({d.comment})"
      msgs := msgs.push m!"[{d.paper} tag {d.tag}{cmt}] corresponds to declaration \
        '{.ofConstName d.declName}'."
    logInfo (MessageData.joinSep msgs.toList "\n")

end PrimeGaps.PaperTag
