# Literals

```agda
module reflection.literals where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import lists.lists
open import foundation-core.dependent-pair-types
open import foundation.cartesian-product-types
open import foundation.booleans
open import foundation.universe-levels
open import foundation.strings
open import foundation.characters
open import foundation.floats
open import foundation.machine-integers
open import foundation.unit-type
open import foundation.identity-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.addition-integers

open import reflection.names
open import reflection.metavariables
open import reflection.fixity
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
