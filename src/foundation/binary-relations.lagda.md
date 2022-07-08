---
title: Binary relations
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.binary-relations where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop-type-Prop; is-prop)
open import foundation.universe-levels using (UU; Level; _⊔_; lsuc)
```

## Idea

A binary relation on a type `A` is a family of types `R x y` depending on two variables `x y : A`. In the special case where each `R x y` is a proposition, we say that the relation is valued in propositions.

## Definition

### Type-valued relations

```agda
Rel : {l1 : Level} (l : Level) (A : UU l1) → UU (l1 ⊔ lsuc l)
Rel l A = A → A → UU l
```

### Relations valued in propositions

```agda
Rel-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Rel-Prop l A = A → (A → UU-Prop l)

type-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) → A → A → UU l2
type-Rel-Prop R x y = pr1 (R x y)

abstract
  is-prop-type-Rel-Prop :
    {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) →
    (x y : A) → is-prop (type-Rel-Prop R x y)
  is-prop-type-Rel-Prop R x y = pr2 (R x y)
```

## Specifications of properties of binary relations

```agda
is-reflexive : {l1 l2 : Level} {A : UU l1} → Rel l2 A → UU (l1 ⊔ l2)
is-reflexive {A = A} R = (x : A) → R x x

is-symmetric : {l1 l2 : Level} {A : UU l1} → Rel l2 A → UU (l1 ⊔ l2)
is-symmetric {A = A} R = (x y : A) → R x y → R y x

is-transitive : {l1 l2 : Level} {A : UU l1} → Rel l2 A → UU (l1 ⊔ l2)
is-transitive {A = A} R = (x y z : A) → R x y → R y z → R x z
```

```agda
is-reflexive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-reflexive-Rel-Prop {A = A} R =
  {x : A} → type-Rel-Prop R x x

is-symmetric-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-symmetric-Rel-Prop {A = A} R =
  {x y : A} → type-Rel-Prop R x y → type-Rel-Prop R y x

is-transitive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-transitive-Rel-Prop {A = A} R =
  {x y z : A} → type-Rel-Prop R x y → type-Rel-Prop R y z → type-Rel-Prop R x z
```
