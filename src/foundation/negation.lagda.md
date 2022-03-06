# Negation

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.negation where

open import foundation-core.negation public

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.empty-types using (empty; is-prop-empty)
open import foundation.logical-equivalences using (_⇔_; _↔_)
open import foundation.propositions using
  ( is-prop; is-prop-function-type; UU-Prop; type-Prop; is-prop-type-Prop)
open import foundation.universe-levels using (UU; Level)
```

## Idea

The Curry-Howard interpretation of negation in type theory is the interpretation of the proposition `P ⇒ ⊥` using propositions as types. Thus, the negation of a type `A` is the type `A → empty`.

## Properties

### The negation of a type is a proposition

```agda
is-prop-neg : {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg {A = A} = is-prop-function-type is-prop-empty

neg-Prop' : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (neg-Prop' A) = ¬ A
pr2 (neg-Prop' A) = is-prop-neg

neg-Prop : {l1 : Level} → UU-Prop l1 → UU-Prop l1
neg-Prop P = neg-Prop' (type-Prop P)
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
    {l1 : Level} (P : UU-Prop l1) → ¬ (P ⇔ neg-Prop P)
  no-fixed-points-neg-Prop P = no-fixed-points-neg (type-Prop P)
```
