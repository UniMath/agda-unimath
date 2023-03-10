# Derivatives of species

```agda
module univalent-combinatorics.derivatives-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

</details>

## Idea

When we think of a species as the coefficients of a formal power series, the derivative of a species is the species representing the derivative of that formal power series.

## Definition

```agda
derivative-species :
  {l1 l2 : Level} → species l1 l2 → species l1 l2
derivative-species F X = F (coprod-𝔽 X unit-𝔽)
```
