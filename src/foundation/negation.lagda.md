---
title: Negation
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.negation where

open import foundation-core.negation public

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.empty-types using (empty; is-prop-empty; ex-falso)
open import foundation.equivalences using (_≃_; map-inv-equiv; map-equiv)
open import foundation.logical-equivalences using (_⇔_; _↔_; equiv-iff')
open import foundation.propositions using
  ( is-prop; is-prop-function-type; Prop; type-Prop; is-prop-type-Prop)
open import foundation.universe-levels using (UU; Level)
```

## Idea

The Curry-Howard interpretation of negation in type theory is the interpretation of the proposition `P ⇒ ⊥` using propositions as types. Thus, the negation of a type `A` is the type `A → empty`.

## Properties

### The negation of a type is a proposition

```agda
is-prop-neg : {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg {A = A} = is-prop-function-type is-prop-empty

neg-Prop' : {l1 : Level} → UU l1 → Prop l1
pr1 (neg-Prop' A) = ¬ A
pr2 (neg-Prop' A) = is-prop-neg

neg-Prop : {l1 : Level} → Prop l1 → Prop l1
neg-Prop P = neg-Prop' (type-Prop P)
```

### Reductio ad absurdum

```agda
reductio-ad-absurdum : {l1 l2 : Level} {P : UU l1} {Q : UU l2} → P → ¬ P → Q
reductio-ad-absurdum p np = ex-falso (np p)
```

### Equivalent types have equivalent negations

```agda
equiv-neg :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  (X ≃ Y) → (¬ X ≃ ¬ Y)
equiv-neg {l1} {l2} {X} {Y} e =
  equiv-iff'
    ( neg-Prop' X)
    ( neg-Prop' Y)
    ( pair (map-neg (map-inv-equiv e)) (map-neg (map-equiv e)))
```

### Negation has no fixed points

```agda
no-fixed-points-neg :
  {l : Level} (A : UU l) → ¬ (A ↔ (¬ A))
no-fixed-points-neg A (pair f g) =
  ( λ (h : ¬ A) → h (g h)) (λ (a : A) → f a a)
```

```agda
abstract
  no-fixed-points-neg-Prop :
    {l1 : Level} (P : Prop l1) → ¬ (P ⇔ neg-Prop P)
  no-fixed-points-neg-Prop P = no-fixed-points-neg (type-Prop P)
```
