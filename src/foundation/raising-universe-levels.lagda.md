# Raising universe levels

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.raising-universe-levels where

open import foundation.dependent-pair-types using (Σ; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; _≃_; is-equiv-has-inverse)
open import foundation.functions using (id; _∘_)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

In Agda, types have a designated universe levels, and universes in Agda don't overlap. Using `data` types we can construct for any type `A` of universe level `l` an equivalent type in any higher universe.

## Definition

```agda
data raise (l : Level) {l1 : Level} (A : UU l1) : UU (l1 ⊔ l) where
  map-raise : A → raise l A

module _
  {l l1 : Level} {A : UU l1}
  where

  map-inv-raise : raise l A → A
  map-inv-raise (map-raise x) = x

  issec-map-inv-raise : (map-raise ∘ map-inv-raise) ~ id
  issec-map-inv-raise (map-raise x) = refl

  isretr-map-inv-raise : (map-inv-raise ∘ map-raise) ~ id
  isretr-map-inv-raise x = refl

  is-equiv-map-raise : is-equiv (map-raise {l} {l1} {A})
  is-equiv-map-raise =
    is-equiv-has-inverse
      map-inv-raise
      issec-map-inv-raise
      isretr-map-inv-raise

equiv-raise : (l : Level) {l1 : Level} (A : UU l1) → A ≃ raise l A
pr1 (equiv-raise l A) = map-raise
pr2 (equiv-raise l A) = is-equiv-map-raise

Raise : (l : Level) {l1 : Level} (A : UU l1) → Σ (UU (l1 ⊔ l)) (λ X → A ≃ X)
pr1 (Raise l A) = raise l A
pr2 (Raise l A) = equiv-raise l A
```
