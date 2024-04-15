# Literals

```agda
module reflection.literals where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import primitives.characters
open import primitives.floats
open import primitives.machine-integers
open import primitives.strings

open import reflection.metavariables
open import reflection.names
```

</details>

## Idea

The `Literal-Agda` type represents literals in Agda.

For concrete examples, see
[`reflection.definitions`](reflection.definitions.md).

## Definition

```agda
data Literal-Agda : UU lzero where
  nat-Literal-Agda : ℕ → Literal-Agda
  word64-Literal-Agda : Word64 → Literal-Agda
  float-Literal-Agda : Float → Literal-Agda
  char-Literal-Agda : Char → Literal-Agda
  string-Literal-Agda : String → Literal-Agda
  quoted-name-Literal-Agda : Name-Agda → Literal-Agda
  metavariable-Literal-Agda : Metavariable-Agda → Literal-Agda
```

## Bindings

```agda
{-# BUILTIN AGDALITERAL Literal-Agda #-}
{-# BUILTIN AGDALITNAT nat-Literal-Agda #-}
{-# BUILTIN AGDALITWORD64 word64-Literal-Agda #-}
{-# BUILTIN AGDALITFLOAT float-Literal-Agda #-}
{-# BUILTIN AGDALITCHAR char-Literal-Agda #-}
{-# BUILTIN AGDALITSTRING string-Literal-Agda #-}
{-# BUILTIN AGDALITQNAME quoted-name-Literal-Agda #-}
{-# BUILTIN AGDALITMETA metavariable-Literal-Agda #-}
```
