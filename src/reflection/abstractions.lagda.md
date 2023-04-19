# Abstractions

```agda
module reflection.abstractions where
```

<details><summary>Imports</summary>

```agda
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
```

</details>

## Idea

-- TODO

## Definition

```agda
data Abs {l} (A : UU l) : UU l where
  abs : (s : String) (x : A) → Abs A

{-# BUILTIN ABS    Abs #-}
{-# BUILTIN ABSABS abs #-}
```
