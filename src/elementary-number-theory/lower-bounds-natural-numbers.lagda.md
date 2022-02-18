# Lower bounds of type families over the natural numbers

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.lower-bounds-natural-numbers where

open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; is-prop-leq-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using
  ( is-prop; is-prop-Π; is-prop-function-type; UU-Prop)
open import foundation.universe-levels using (Level; UU)
```

## Idea

A lower bound for a type family `P` over the natural numbers is a natural number `n` such that `P x → n ≤ x` for all `x : ℕ`.

## Definition

```agda
is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-lower-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ n m
```

## Properties

### Being a lower bound is a property

```agda
module _
  {l1 : Level} {P : ℕ → UU l1}
  where

  abstract
    is-prop-is-lower-bound-ℕ : (x : ℕ) → is-prop (is-lower-bound-ℕ P x)
    is-prop-is-lower-bound-ℕ x =
      is-prop-Π (λ y → is-prop-function-type (is-prop-leq-ℕ x y))

  is-lower-bound-ℕ-Prop : (x : ℕ) → UU-Prop l1
  pr1 (is-lower-bound-ℕ-Prop x) = is-lower-bound-ℕ P x
  pr2 (is-lower-bound-ℕ-Prop x) = is-prop-is-lower-bound-ℕ x
```
