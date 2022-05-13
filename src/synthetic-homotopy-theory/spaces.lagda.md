---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.spaces where

open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.24-pushouts

--------------------------------------------------------------------------------

-- Examples of pushouts
unit-pt : Pointed-Type lzero
unit-pt = pair unit star

is-contr-pt :
  {l : Level} → Pointed-Type l → UU l
is-contr-pt A = is-contr (pr1 A)
```
