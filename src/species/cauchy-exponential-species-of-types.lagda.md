# Cauchy exponential of species of types

```agda
module species.cauchy-exponential-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.relaxed-sigma-decompositions
open import foundation.sigma-decomposition-subuniverse
open import foundation.small-types
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Definition

```agda
cauchy-exponential-species-types :
  {l1 l2 : Level } → species-types l1 l2 → species-types l1 (lsuc l1 ⊔ l2)
cauchy-exponential-species-types {l1} {l2} S X =
  Σ ( Relaxed-Σ-Decomposition l1 l1 X)
    ( λ D →
      ( b : indexing-type-Relaxed-Σ-Decomposition D) →
      ( S (cotype-Relaxed-Σ-Decomposition D b)))
```
