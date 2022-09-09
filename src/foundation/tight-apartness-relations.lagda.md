---
title: Tight apartness relations
---

```agda
module foundation.tight-apartness-relations where

open import foundation.apartness-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

## Idea

A relation `R` is said to be tight if for every `x y : A` we have `¬ (R x y) → (x ＝ y)`. 

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : A → A → UU-Prop l2)
  where

  is-tight : UU (l1 ⊔ l2)
  is-tight = (x y : A) → ¬ (type-Prop (R x y)) → x ＝ y

  is-tight-apartness-relation : UU (l1 ⊔ l2)
  is-tight-apartness-relation =
    is-apartness-relation R × is-tight

is-tight-Apartness-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Apartness-Relation l2 A) → UU (l1 ⊔ l2)
is-tight-Apartness-Relation R = is-tight (rel-Apartness-Relation R)

Tight-Apartness-Relation :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Tight-Apartness-Relation l2 A =
  Σ (Apartness-Relation l2 A) (λ R → is-tight-Apartness-Relation R)

module _
  {l1 l2 : Level} {A : UU l1} (R : Tight-Apartness-Relation l2 A)
  where

  apartness-relation-Tight-Apartness-Relation :
    Apartness-Relation l2 A
  apartness-relation-Tight-Apartness-Relation = pr1 R

  is-tight-apartness-relation-Tight-Apartness-Relation :
    is-tight-Apartness-Relation apartness-relation-Tight-Apartness-Relation
  is-tight-apartness-relation-Tight-Apartness-Relation = pr2 R
```
