# Raising universe levels

```agda
module foundation.raising-universe-levels where

open import foundation-core.raising-universe-levels public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-contractible-types
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
open import foundation-core.subtypes
```

</details>

## Idea

In Agda, types have a designated universe levels, and universes in Agda don't
overlap. Using `data` types we can construct for any type `A` of universe level
`l` an equivalent type in any higher universe.

## Properties

### Raising universe levels of subtypes

```agda
raise-subtype :
  (l : Level) {l1 l2 : Level} {A : UU l1} →
  subtype l2 A → subtype (l2 ⊔ l) A
raise-subtype l B x = raise-Prop l (B x)

compute-raise-subtype :
  (l : Level) → {l1 l2 : Level} → {A : UU l1} →
  (S : subtype l2 A) → type-subtype S ≃ type-subtype (raise-subtype l S)
compute-raise-subtype l S = equiv-tot (compute-raise l ∘ type-Prop ∘ S)
```

### Raising universe levels from `l1` to `l ⊔ l1` is an embedding from `UU l1` to `UU (l ⊔ l1)`

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
