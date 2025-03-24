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
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
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

### Raising universe levels from `l1` to `l ⊔ l1` is an embedding from `UU l1` to `UU (l ⊔ l1)`

```agda
abstract
  is-emb-raise : (l : Level) {l1 : Level} → is-emb (raise l {l1})
  is-emb-raise l {l1} =
    is-emb-is-prop-map
      ( λ X →
        is-prop-is-proof-irrelevant
          ( λ (A , p) →
            is-contr-equiv
              ( Σ (UU l1) (λ A' → A' ≃ A))
              ( equiv-tot
                ( λ A' →
                  ( equiv-postcomp-equiv (inv-equiv (compute-raise l A)) A') ∘e
                  ( equiv-precomp-equiv (compute-raise l A') (raise l A)) ∘e
                  ( equiv-univalence) ∘e
                  ( equiv-concat' (raise l A') (inv p))))
              ( is-torsorial-equiv' A)))

emb-raise : (l : Level) {l1 : Level} → UU l1 ↪ UU (l1 ⊔ l)
pr1 (emb-raise l) = raise l
pr2 (emb-raise l) = is-emb-raise l
```
