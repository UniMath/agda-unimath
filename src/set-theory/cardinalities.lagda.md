---
title: Cardinalities of sets
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module set-theory.cardinalities where

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.universe-levels
```

## Idea

The cardinality of a set is its isomorphism class. We take isomorphism classes of sets by set truncating the universe of sets of any given universe level. Note that this definition takes advantage of the univalence axiom: By the univalence axiom isomorphic sets are equal, and will be mapped to the same element in the set truncation of the universe of all sets.

## Definition

```agda
cardinal-Set : (l : Level) → UU-Set (lsuc l)
cardinal-Set l = trunc-Set (UU-Set l)

cardinal : (l : Level) → UU (lsuc l)
cardinal l = type-Set (cardinal-Set l)

card : {l : Level} → UU-Set l → cardinal l
card A = unit-trunc-Set A

leq-card-Prop : {l1 l2 : Level} → cardinal l1 → cardinal l2 → UU-Prop (l1 ⊔ l2)
leq-card-Prop {l1} {l2} X Y =
  apply-universal-property-trunc-Set X
    ( UU-Prop-Set (l1 ⊔ l2))
    ( λ X' →
      apply-universal-property-trunc-Set Y
        ( UU-Prop-Set (l1 ⊔ l2))
        ( λ Y' → trunc-Prop (type-Set X' ↪ type-Set Y')))

_≤-card_ : {l1 l2 : Level} → cardinal l1 → cardinal l2 → UU (l1 ⊔ l2)
X ≤-card Y = type-Prop (leq-card-Prop X Y)

is-prop-≤-card : {l : Level} {X Y : cardinal l} → is-prop (X ≤-card Y)
is-prop-≤-card {X = X} {Y = Y} = is-prop-type-Prop (leq-card-Prop X Y)

compute-leq-card :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) →
  type-trunc-Prop (type-Set A ↪ type-Set B) ≃ (card A ≤-card card B)
compute-leq-card A B = ?

refl-≤-card : {l : Level} (X : cardinal l) → X ≤-card X
refl-≤-card {l} =
  apply-dependent-universal-property-trunc-Set
    ( λ X → set-Prop (leq-card-Prop X X))
    ( λ A → {!unit-trunc-Prop ?!})
```
