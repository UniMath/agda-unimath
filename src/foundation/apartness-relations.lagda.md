---
title: Apartness relations
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.apartness-relations where

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.disjunction
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

## Idea

An apartness relation on a type `A` is a relation `R` which is

  - Antireflexive: For any `a : A` we have `¬ (R a a)`
  - Symmetric: For any `a b : A` we have `R a b → R b a`
  - Cotransitive: For any `a b c : A` we have `R a b → R a c ∨ R b c`.

The idea of an apartness relation `R` is that `R a b` holds if you can positively establish a difference between `a` and `b`. For example, two subsets `A` and `B` of a type `X` are apart if we can find an element that is in the symmetric difference of `A` and `B`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : A → A → UU-Prop l2)
  where

  is-antireflexive : UU (l1 ⊔ l2)
  is-antireflexive = (a : A) → ¬ (type-Prop (R a a))

  is-cotransitive : UU (l1 ⊔ l2)
  is-cotransitive =
    (a b c : A) → type-hom-Prop (R a b) (disj-Prop (R a c) (R b c))

  is-apartness-relation : UU (l1 ⊔ l2)
  is-apartness-relation =
    ( is-antireflexive) ×
    ( ( is-symmetric ((λ x y → type-Prop (R x y)))) ×
      ( is-cotransitive))
```
