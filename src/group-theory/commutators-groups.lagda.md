---
title: Commutators of elements in groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.commutators-groups where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equational-reasoning
open import foundation.identity-types using
  ( Id; _＝_; ap-binary; inv; _∙_; ap; refl)
open import foundation.sets using (UU-Set; is-set; Id-Prop)
open import foundation.universe-levels using (Level; UU; lsuc)

open import group-theory.groups

```

## Idea

A commutator gives an indication of the extent to which a group multiplication fails to be commutative.

The commutator of two elements, g and h, of a group G, is the element `[g, h] = g∙hg⁻¹h⁻¹`.

https://en.wikipedia.org/wiki/Commutator#Group_theory

## Definition

```agda
module _
  {l : Level} (G : Group l)
  where

  commutator-Group : type-Group G → type-Group G → type-Group G
  commutator-Group x y = right-div-Group G (mul-Group G x y) (mul-Group G y x)
```

## Properties

### The commutator of x and y is unit if and only x and y commutes

We first introduce some shorter names to make the proofs less verbose

```agda
  is-unit-commutator-commute-Group :
    (x y : type-Group G) →
    commute-Group G x y → is-unit-Group G (commutator-Group x y)
  is-unit-commutator-commute-Group x y commutes =
    is-unit-right-div-eq-Group G commutes

  commute-is-unit-commutator-Group :
    (x y : type-Group G) →
    is-unit-Group G (commutator-Group x y) → commute-Group G x y
  commute-is-unit-commutator-Group x y comm-unit =
    eq-is-unit-right-div-Group G comm-unit

  inv-commutator-Group : ∀ x y → inv-Group G (commutator-Group x y) ＝ commutator-Group y x
  inv-commutator-Group x y = inv-right-div-Group G (mul-Group G x y) (mul-Group G y x)
```

### Demonstration of the group solver

{-
  private
    _*_ = mul-Group G
    infixl 30 _*_
    _⁻¹ = inv-Group G
    infix 40 _⁻¹
    unit = unit-Group G

  open import group-theory.group-solver
  private
    _*'_ : ∀ {n} → GroupSyntax n → GroupSyntax n → GroupSyntax n
    _*'_ = gMul
    infixl 20 _*'_
  inv-Commutator-law' : ∀ x y → inv-Group G (commutator-Group x y) ＝ commutator-Group y x
  inv-Commutator-law' x y = simplifyExpr G ? ?
  -- simplifyExpr G (x ∷ y ∷ empty-vec) (λ x y → gInv (x *' y *' gInv x *' gInv y))

  commutes-when-commutor-is-unit' :
    ∀ x y → (commutator-Group x y ＝ unit-Group G) → mul-Group G x y ＝ mul-Group G y x
  commutes-when-commutor-is-unit' x y comm-unit =
    x * y                         ＝ by inv (simplifyExpr G (x ∷ (y ∷ empty-vec)) (λ x y → (x *' y *' gInv x *' gInv y *' y *' x))) to
    x * y * x ⁻¹ * y ⁻¹ * y * x   ＝ by ap (λ z → z * y * x) comm-unit to
    unit * y * x                  ＝ by simplifyExpr G (x ∷ (y ∷ empty-vec)) (λ x y → (gUnit *' y *' x)) to
    y * x                         ∎

  commutor-is-unit-when-commutes' :
    ∀ x y → (mul-Group G x y ＝ mul-Group G y x) → commutator-Group x y ＝ unit-Group G
  commutor-is-unit-when-commutes' x y commutes =
    x * y * x ⁻¹ * y ⁻¹ ＝ by ap (λ z → z * x ⁻¹ * y ⁻¹) commutes to
    y * x * x ⁻¹ * y ⁻¹ ＝ by simplifyExpr G (x ∷ y ∷ empty-vec) (λ x y → (y *' x *' gInv x *' gInv y)) to
    unit                  ∎
-}
```
