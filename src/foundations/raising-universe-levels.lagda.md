---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.raising-universe-levels where

open import foundations.dependent-pair-types using (Σ; pr1; pr2)
open import foundations.empty-type using (empty)
open import foundations.equivalences using
  ( is-equiv; _≃_; is-equiv-has-inverse)
open import foundations.functions using (id; _∘_)
open import foundations.homotopies using (_~_)
open import foundations.identity-types using (Id; refl)
open import foundations.levels using (Level; UU; _⊔_)
open import foundations.unit-type using (unit; star)
```

# Raising universe levels

This file contains the equivalence from any type A : UU l1 to a larger universe UU (l1 ⊔ l2)

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

```agda
raise-empty : (l : Level) → UU l
raise-empty l = raise l empty

equiv-raise-empty : (l : Level) → empty ≃ raise-empty l
equiv-raise-empty l = equiv-raise l empty
```

```agda
raise-unit : (l : Level) → UU l
raise-unit l = raise l unit

raise-star : {l : Level} → raise l unit
raise-star = map-raise star

equiv-raise-unit : (l : Level) → unit ≃ raise-unit l
equiv-raise-unit l = equiv-raise l unit
```
