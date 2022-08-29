---
title: Group commutators
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.commutators-groups where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equational-reasoning using (step-equational-reasoning ; _∎)
open import foundation.identity-types using (Id; _＝_; ap-binary; inv; _∙_; ap; refl)
open import foundation.sets using (UU-Set; is-set; Id-Prop)
open import foundation.universe-levels using (Level; UU; lsuc)

open import group-theory.groups using
  ( Group; type-Group; mul-Group; set-Group; is-set-type-Group
  ; inv-Group ; unit-Group ; associative-mul-Group
  ; right-inverse-law-mul-Group
  ; left-inverse-law-mul-Group
  ; right-unit-law-mul-Group
  ; left-unit-law-mul-Group
  )

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
  commutator-Group x y = mul-Group G (mul-Group G (mul-Group G x y) (inv-Group G x)) (inv-Group G y)
  -- commutator-Group x y = x * y * x ⁻¹ * y ⁻¹

```

## Properties

### The commutator of x and y is unit if and only x and y commutes

```agda

  private
    -- Shorter names to make proofs less verbose
    _*_ = mul-Group G
    infixl 30 _*_
    _⁻¹ = inv-Group G
    infix 40 _⁻¹
    unit = unit-Group G

    -- [_,_] = commutator-Group

  commutor-is-unit-when-commutes : ∀ x y → (mul-Group G x y ＝ mul-Group G y x) → commutator-Group x y ＝ unit-Group G
  commutor-is-unit-when-commutes x y commutes =
    commutator-Group x y  ＝ by refl to
    (x * y) * x ⁻¹ * y ⁻¹ ＝ by ap (λ z → (z * (x ⁻¹)) * (y ⁻¹)) commutes to
    (y * x) * x ⁻¹ * y ⁻¹ ＝ by ap (_* (y ⁻¹)) (associative-mul-Group G y x (x ⁻¹)) to
    y * (x * x ⁻¹) * y ⁻¹ ＝ by ap (λ z → (y * z) * (y ⁻¹)) (right-inverse-law-mul-Group G x) to
    (y * unit) * y ⁻¹     ＝ by ap (_* (y ⁻¹)) (right-unit-law-mul-Group G y) to
    y * y ⁻¹              ＝ by right-inverse-law-mul-Group G y to
    unit                  ∎

  commutes-when-commutor-is-unit : ∀ x y → (commutator-Group x y ＝ unit-Group G) → mul-Group G x y ＝ mul-Group G y x
  commutes-when-commutor-is-unit x y comm-unit =
    x * y                         ＝ by inv (right-unit-law-mul-Group G (x * y)) to
    x * y * unit                  ＝ by ap (λ z → (x * y) * z) (inv (left-inverse-law-mul-Group G x)) to
    x * y * (x ⁻¹ * x)            ＝ by inv (associative-mul-Group G (x * y) (x ⁻¹) x) to
    x * y * x ⁻¹ * x              ＝ by ap (_* x) (inv (right-unit-law-mul-Group G (x * y * x ⁻¹))) to
    x * y * x ⁻¹ * unit * x       ＝ by ap (λ z → x * y * x ⁻¹ * z * x)
                                           (inv (left-inverse-law-mul-Group G y)) to
    x * y * x ⁻¹ * (y ⁻¹ * y) * x ＝ by ap (_* x) (inv (associative-mul-Group G (x * y * x ⁻¹) (y ⁻¹) y)) to
    x * y * x ⁻¹ * y ⁻¹ * y * x   ＝ by refl to
    commutator-Group x y * y * x  ＝ by ap (λ z → z * y * x) comm-unit to
    unit * y * x                  ＝ by ap (_* x) (left-unit-law-mul-Group G y) to
    y * x                         ∎
```
