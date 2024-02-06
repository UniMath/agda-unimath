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
  nat : (n : ℕ) → Literal-Agda
  word64 : (n : Word64) → Literal-Agda
  float : (x : Float) → Literal-Agda
  char : (c : Char) → Literal-Agda
  string : (s : String) → Literal-Agda
  name : (x : Name-Agda) → Literal-Agda
  meta : (x : Metavariable-Agda) → Literal-Agda

{-# BUILTIN AGDALITERAL Literal-Agda #-}
{-# BUILTIN AGDALITNAT nat #-}
{-# BUILTIN AGDALITWORD64 word64 #-}
{-# BUILTIN AGDALITFLOAT float #-}
{-# BUILTIN AGDALITCHAR char #-}
{-# BUILTIN AGDALITSTRING string #-}
{-# BUILTIN AGDALITQNAME name #-}
{-# BUILTIN AGDALITMETA meta #-}
```
