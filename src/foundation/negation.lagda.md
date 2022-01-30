# Negation

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.negation where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (pair)
open import foundation.empty-types using (empty)
open import foundation.universe-levels using (UU; Level)
```

## Idea

The Curry-Howard interpretation of negation in type theory is the interpretation of the proposition `P ⇒ ⊥` using propositions as types. Thus, the negation of a type `A` is the type `A → empty`.

## Definition

```agda
¬ : {l : Level} → UU l → UU l
¬ A = A → empty

map-neg : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬ Q → ¬ P)
map-neg f nq p = nq (f p)
```

## Properties

### Negation has no fixed points

```agda
no-fixed-points-neg :
  {l : Level} (A : UU l) → ¬ ((A → ¬ A) × (¬ A → A))
no-fixed-points-neg A (pair f g) =
  ( λ (h : ¬ A) → h (g h)) (λ (a : A) → f a a)
```
