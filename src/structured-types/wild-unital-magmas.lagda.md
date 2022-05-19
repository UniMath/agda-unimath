---
title: Wild unital magmas
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module structured-types.wild-unital-magmas where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (id)
open import foundation.homotopies using (nat-htpy; _~_)
open import foundation.identity-types using
  ( Id; refl; ap-binary; _∙_; left-unit; right-unit; ap; concat; inv; ap-id;
    assoc; triangle-ap-binary; triangle-ap-binary')
open import foundation.path-algebra using
  ( horizontal-concat-Id²)
open import foundation.universe-levels using (UU; Level; lsuc; _⊔_)

open import group-theory.homomorphisms-semigroups using (preserves-mul)

open import structured-types.magmas
open import structured-types.pointed-maps using (_→*_)
open import structured-types.pointed-types using
  ( Pointed-Type; type-Pointed-Type; pt-Pointed-Type)
```

## Idea

A wild unital magma is a pointed type equipped with a binary operation for which the base point is a unit

## Definition

### Wild unital magmas

```agda
is-unital-mul-Pointed-Type :
  {l : Level} (A : Pointed-Type l)
  (μ : (x y : type-Pointed-Type A) → type-Pointed-Type A) → UU l
is-unital-mul-Pointed-Type A μ =
  Σ ( (x : type-Pointed-Type A) → Id (μ (pt-Pointed-Type A) x) x)
      ( λ α →
        Σ ( (x : type-Pointed-Type A) → Id (μ x (pt-Pointed-Type A)) x)
          ( λ β → Id (α (pt-Pointed-Type A)) (β (pt-Pointed-Type A))))

unital-mul-Pointed-Type :
  {l : Level} → Pointed-Type l → UU l
unital-mul-Pointed-Type A =
  Σ ( type-Pointed-Type A → type-Pointed-Type A → type-Pointed-Type A)
    ( is-unital-mul-Pointed-Type A)

Wild-Unital-Magma : (l : Level) → UU (lsuc l)
Wild-Unital-Magma l =
  Σ ( Pointed-Type l) unital-mul-Pointed-Type

module _
  {l : Level} (M : Wild-Unital-Magma l)
  where

  pointed-type-Wild-Unital-Magma : Pointed-Type l
  pointed-type-Wild-Unital-Magma = pr1 M
  
  type-Wild-Unital-Magma : UU l
  type-Wild-Unital-Magma = type-Pointed-Type pointed-type-Wild-Unital-Magma

  unit-Wild-Unital-Magma : type-Wild-Unital-Magma
  unit-Wild-Unital-Magma = pt-Pointed-Type pointed-type-Wild-Unital-Magma

  unital-mul-Wild-Unital-Magma :
    unital-mul-Pointed-Type pointed-type-Wild-Unital-Magma
  unital-mul-Wild-Unital-Magma = pr2 M

  mul-Wild-Unital-Magma :
    type-Wild-Unital-Magma → type-Wild-Unital-Magma → type-Wild-Unital-Magma
  mul-Wild-Unital-Magma = pr1 unital-mul-Wild-Unital-Magma

  mul-Wild-Unital-Magma' :
    type-Wild-Unital-Magma → type-Wild-Unital-Magma → type-Wild-Unital-Magma
  mul-Wild-Unital-Magma' x y = mul-Wild-Unital-Magma y x

  ap-mul-Wild-Unital-Magma :
    {a b c d : type-Wild-Unital-Magma} → Id a b → Id c d →
    Id (mul-Wild-Unital-Magma a c) (mul-Wild-Unital-Magma b d)
  ap-mul-Wild-Unital-Magma p q = ap-binary mul-Wild-Unital-Magma p q

  magma-Wild-Unital-Magma : Magma l
  pr1 magma-Wild-Unital-Magma = type-Wild-Unital-Magma
  pr2 magma-Wild-Unital-Magma = mul-Wild-Unital-Magma

  left-unit-law-mul-Wild-Unital-Magma :
    (x : type-Wild-Unital-Magma) →
    Id (mul-Wild-Unital-Magma unit-Wild-Unital-Magma x) x
  left-unit-law-mul-Wild-Unital-Magma =
    pr1 (pr2 unital-mul-Wild-Unital-Magma)

  right-unit-law-mul-Wild-Unital-Magma :
    (x : type-Wild-Unital-Magma) →
    Id (mul-Wild-Unital-Magma x unit-Wild-Unital-Magma) x
  right-unit-law-mul-Wild-Unital-Magma =
    pr1 (pr2 (pr2 unital-mul-Wild-Unital-Magma))

  coh-unit-laws-mul-Wild-Unital-Magma :
    Id ( left-unit-law-mul-Wild-Unital-Magma unit-Wild-Unital-Magma)
       ( right-unit-law-mul-Wild-Unital-Magma unit-Wild-Unital-Magma)
  coh-unit-laws-mul-Wild-Unital-Magma =
    pr2 (pr2 (pr2 unital-mul-Wild-Unital-Magma))
```
