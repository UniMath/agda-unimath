# Raising universe levels

```agda
module foundation.raising-universe-levels where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

In Agda, types have a designated universe levels, and universes in Agda don't
overlap. Using `data` types we can construct for any type `A` of universe level
`l` an equivalent type in any higher universe.

## Definition

```agda
data raise (l : Level) {l1 : Level} (A : UU l1) : UU (l1 ⊔ l) where
  map-raise : A → raise l A

data raiseω {l1 : Level} (A : UU l1) : UUω where
  map-raiseω : A → raiseω A
```

## Properties

### Types are equivalent to their raised equivalents

```agda
module _
  {l l1 : Level} {A : UU l1}
  where

  map-inv-raise : raise l A → A
  map-inv-raise (map-raise x) = x

  is-section-map-inv-raise : (map-raise ∘ map-inv-raise) ~ id
  is-section-map-inv-raise (map-raise x) = refl

  is-retraction-map-inv-raise : (map-inv-raise ∘ map-raise) ~ id
  is-retraction-map-inv-raise x = refl

  is-equiv-map-raise : is-equiv (map-raise {l} {l1} {A})
  is-equiv-map-raise =
    is-equiv-is-invertible
      map-inv-raise
      is-section-map-inv-raise
      is-retraction-map-inv-raise

compute-raise : (l : Level) {l1 : Level} (A : UU l1) → A ≃ raise l A
pr1 (compute-raise l A) = map-raise
pr2 (compute-raise l A) = is-equiv-map-raise

inv-compute-raise : (l : Level) {l1 : Level} (A : UU l1) → raise l A ≃ A
inv-compute-raise l A = inv-equiv (compute-raise l A)

Raise : (l : Level) {l1 : Level} (A : UU l1) → Σ (UU (l1 ⊔ l)) (λ X → A ≃ X)
pr1 (Raise l A) = raise l A
pr2 (Raise l A) = compute-raise l A
```

### Raising universe levels of sets

```agda
raise-Set : (l : Level) {l1 : Level} → Set l1 → Set (l ⊔ l1)
pr1 (raise-Set l A) = raise l (type-Set A)
pr2 (raise-Set l A) =
  is-set-equiv' (type-Set A) (compute-raise l (type-Set A)) (is-set-type-Set A)
```

### Raising equivalent types

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-equiv-raise : raise l3 A → raise l4 B
  map-equiv-raise (map-raise x) = map-raise (map-equiv e x)

  map-inv-equiv-raise : raise l4 B → raise l3 A
  map-inv-equiv-raise (map-raise y) = map-raise (map-inv-equiv e y)

  is-section-map-inv-equiv-raise :
    ( map-equiv-raise ∘ map-inv-equiv-raise) ~ id
  is-section-map-inv-equiv-raise (map-raise y) =
    ap map-raise (is-section-map-inv-equiv e y)

  is-retraction-map-inv-equiv-raise :
    ( map-inv-equiv-raise ∘ map-equiv-raise) ~ id
  is-retraction-map-inv-equiv-raise (map-raise x) =
    ap map-raise (is-retraction-map-inv-equiv e x)

  is-equiv-map-equiv-raise : is-equiv map-equiv-raise
  is-equiv-map-equiv-raise =
    is-equiv-is-invertible
      map-inv-equiv-raise
      is-section-map-inv-equiv-raise
      is-retraction-map-inv-equiv-raise

  equiv-raise : raise l3 A ≃ raise l4 B
  pr1 equiv-raise = map-equiv-raise
  pr2 equiv-raise = is-equiv-map-equiv-raise
```

### Raising universe levels from `l1` to `l1 ⊔ l2` is an embedding from `UU l1` to `UU (l1 ⊔ l2)`

```agda
module _
  (l2 : Level) {l1 : Level}
  where

  abstract
    is-proof-irrelevant-map-raise :
      (X : UU (l1 ⊔ l2)) → is-proof-irrelevant (fiber (raise l2 {l1}) X)
    is-proof-irrelevant-map-raise X (A , p) =
      is-contr-equiv
        ( Σ (UU l1) (λ A' → A' ≃ A))
        ( equiv-tot
          ( λ A' →
            ( equiv-postcomp-equiv (inv-compute-raise l2 A) A') ∘e
            ( equiv-precomp-equiv (compute-raise l2 A') (raise l2 A)) ∘e
            ( equiv-univalence) ∘e
            ( equiv-concat' (raise l2 A') (inv p))))
        ( is-torsorial-equiv' A)

  abstract
    is-prop-map-raise : is-prop-map (raise l2 {l1})
    is-prop-map-raise X =
      is-prop-is-proof-irrelevant (is-proof-irrelevant-map-raise X)

  abstract
    is-emb-raise : is-emb (raise l2 {l1})
    is-emb-raise = is-emb-is-prop-map is-prop-map-raise

  emb-raise : UU l1 ↪ UU (l1 ⊔ l2)
  emb-raise = (raise l2 , is-emb-raise)
```
