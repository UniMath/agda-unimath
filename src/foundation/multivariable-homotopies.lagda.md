# Homotopies of multivariable operations

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.multivariable-homotopies where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.multivariable-operations
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.functions

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given two multivariable operations `f` and `g`, the type of multivariable
homotopies between `f` and `g` is defined to be the type of pointwise
identifications of `f` and `g`. We show that this characterizes the identity
type of multivariable operations.

## Definition

```agda
module _
  { l1 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( X : UU l1)
  where

  multivariable-htpy :
    multivariable-operation n As X →
    multivariable-operation n As X →
    UU l1
  multivariable-htpy f g =
    ( as : multivariable-input n As) →
    ( apply-multivariable-operation n As X f as) ＝
      ( apply-multivariable-operation n As X g as)

  refl-multivariable-htpy :
    (f : multivariable-operation n As X) →
    multivariable-htpy f f
  refl-multivariable-htpy f as = refl

  multivariable-htpy-eq :
    ( f g : multivariable-operation n As X) →
    ( f ＝ g) →
    multivariable-htpy f g
  multivariable-htpy-eq f .f refl = refl-multivariable-htpy f

multivariable-eq-htpy :
  { l1 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( X : UU l1)
  ( f g : multivariable-operation n As X) →
  multivariable-htpy n As X f g →
  ( f ＝ g)
multivariable-eq-htpy zero-ℕ As X f g h =
  h (empty-multivariable-input As)
multivariable-eq-htpy (succ-ℕ n) As X f g h =
  eq-htpy
    ( λ a0 →
      multivariable-eq-htpy n
        ( tail-functional-vec n As)
        ( X)
        ( f a0)
        ( g a0)
        ( λ as → h (cons-multivariable-input' n As a0 as)))
```
