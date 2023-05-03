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

The `Literal` type represents literals in Agda.

For concrete examples, see
[`reflection.definitions`](reflection.definitions.md).

## Definition

```agda
data Literal : UU lzero where
  nat : (n : ℕ) → Literal
  word64 : (n : Word64) → Literal
  float : (x : Float) → Literal
  char : (c : Char) → Literal
  string : (s : String) → Literal
  name : (x : Name) → Literal
  meta : (x : Meta) → Literal

{-# BUILTIN AGDALITERAL Literal #-}
{-# BUILTIN AGDALITNAT nat #-}
{-# BUILTIN AGDALITWORD64 word64 #-}
{-# BUILTIN AGDALITFLOAT float #-}
{-# BUILTIN AGDALITCHAR char #-}
{-# BUILTIN AGDALITSTRING string #-}
{-# BUILTIN AGDALITQNAME name #-}
{-# BUILTIN AGDALITMETA meta #-}
```
