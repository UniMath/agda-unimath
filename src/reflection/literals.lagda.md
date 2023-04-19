# Literals

```agda
module reflection.literals where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.characters
open import foundation.floats
open import foundation.identity-types
open import foundation.machine-integers
open import foundation.strings
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.dependent-pair-types

open import lists.lists

open import reflection.fixity
open import reflection.metavariables
open import reflection.names
```

</details>

## Idea

-- TODO

## Definition

```agda
data Literal : UU lzero where
  nat    : (n : ℕ)    → Literal
  word64 : (n : Word64) → Literal
  float  : (x : Float)  → Literal
  char   : (c : Char)   → Literal
  string : (s : String) → Literal
  name   : (x : Name)   → Literal
  meta   : (x : Meta)   → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITWORD64 word64  #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITQNAME  name    #-}
{-# BUILTIN AGDALITMETA   meta    #-}
```
