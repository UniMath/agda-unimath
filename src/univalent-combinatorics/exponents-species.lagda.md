# Exponents of species

```agda
module univalent-combinatorics.exponents-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.morphisms-species
open import univalent-combinatorics.species
```

</details>

## Idea

The exponent of two species `F` and `G` is the pointwise exponent

## Definition

### Exponents of species

```agda
function-species :
  {l1 l2 l3 : Level} → species l1 l2 → species l1 l3 → 𝔽 l1 → UU (l2 ⊔ l3)
function-species F G X = F X → G X
```
