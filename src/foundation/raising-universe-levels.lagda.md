---
title: Raising universe levels
---

```agda
module foundation.raising-universe-levels where

open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.universe-levels
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

compute-raise : (l : Level) {l1 : Level} (A : UU l1) → A ≃ raise l A
pr1 (compute-raise l A) = map-raise
pr2 (compute-raise l A) = is-equiv-map-raise

Raise : (l : Level) {l1 : Level} (A : UU l1) → Σ (UU (l1 ⊔ l)) (λ X → A ≃ X)
pr1 (Raise l A) = raise l A
pr2 (Raise l A) = compute-raise l A
```

### Raising universe levels of propositions

```agda
raise-Prop : (l : Level) {l1 : Level} → Prop l1 → Prop (l ⊔ l1)
pr1 (raise-Prop l P) = raise l (type-Prop P)
pr2 (raise-Prop l P) =
  is-prop-equiv' (compute-raise l (type-Prop P)) (is-prop-type-Prop P)
```

### Raising universe levels of sets

```agda
raise-Set : (l : Level) {l1 : Level} → Set l1 → Set (l ⊔ l1)
pr1 (raise-Set l A) = raise l (type-Set A)
pr2 (raise-Set l A) =
  is-set-equiv' (type-Set A) (compute-raise l (type-Set A)) (is-set-type-Set A)
```
