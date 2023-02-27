# Generalized species

```agda
module univalent-combinatorics.generalized-species where

open import foundation.universe-levels
open import foundation.dependent-pair-types

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.general-species
open import univalent-combinatorics.species
```

## Definitions

```agda
module _
  {l1 l2 : Level} (S : species l1 l2)
  where

  Σ-generalized-species :
    general-species (l1) (l1 ⊔ l2)
  Σ-generalized-species X =
    Σ (is-finite X) (λ p → S (X , p))

  Π-generalized-species :
    general-species (l1) (l1 ⊔ l2)
  Π-generalized-species X =
    (p : is-finite X) → S (X , p)
```
