# Decidable subposets

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.decidable-subposets where

open import foundation.decidable-propositions using (decidable-Prop)
open import foundation.decidable-subtypes using (subtype-decidable-subtype)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositions using (Prop; is-prop)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import order-theory.posets using (Poset; element-Poset)
open import order-theory.subposets using
  ( element-sub-Poset; eq-element-sub-Poset; leq-sub-poset-Prop; leq-sub-Poset;
    is-prop-leq-sub-Poset; refl-leq-sub-Poset; transitive-leq-sub-Poset;
    sub-Poset)
```

## Definition

```agda

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2)
  (S : element-Poset X → decidable-Prop l3)
  where

  element-decidable-sub-Poset : UU (l1 ⊔ l3)
  element-decidable-sub-Poset =
    element-sub-Poset X (subtype-decidable-subtype S)

  eq-element-decidable-sub-Poset :
    (x y : element-decidable-sub-Poset) → Id (pr1 x) (pr1 y) → Id x y
  eq-element-decidable-sub-Poset =
    eq-element-sub-Poset X (subtype-decidable-subtype S)

  leq-decidable-sub-poset-Prop :
    (x y : element-decidable-sub-Poset) → Prop l2
  leq-decidable-sub-poset-Prop =
    leq-sub-poset-Prop X (subtype-decidable-subtype S)

  leq-decidable-sub-Poset : (x y : element-decidable-sub-Poset) → UU l2
  leq-decidable-sub-Poset =
    leq-sub-Poset X (subtype-decidable-subtype S)

  is-prop-leq-decidable-sub-Poset :
    (x y : element-decidable-sub-Poset) →
    is-prop (leq-decidable-sub-Poset x y)
  is-prop-leq-decidable-sub-Poset =
    is-prop-leq-sub-Poset X (subtype-decidable-subtype S)

  refl-leq-decidable-sub-Poset :
    (x : element-decidable-sub-Poset) → leq-decidable-sub-Poset x x
  refl-leq-decidable-sub-Poset =
    refl-leq-sub-Poset X (subtype-decidable-subtype S)

  transitive-leq-decidable-sub-Poset :
    (x y z : element-decidable-sub-Poset) →
    leq-decidable-sub-Poset y z → leq-decidable-sub-Poset x y →
    leq-decidable-sub-Poset x z
  transitive-leq-decidable-sub-Poset =
    transitive-leq-sub-Poset X (subtype-decidable-subtype S)

  decidable-sub-Poset : Poset (l1 ⊔ l3) l2
  decidable-sub-Poset = sub-Poset X (subtype-decidable-subtype S)
```
