# Pointing of species

```agda
module univalent-combinatorics.pointing-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

</details>

## Idea

A pointing of a species `F` is the species `F*` given by `F* X := X × (F X)`. In other words, it is the species of pointed `F`-structures

## Definition

```agda
pointing-species : {l1 l2 : Level} → species l1 l2 → species l1 (l1 ⊔ l2)
pointing-species F X = type-𝔽 X × F X
```
