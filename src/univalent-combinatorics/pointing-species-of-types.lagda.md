# Pointing of species

```agda
module univalent-combinatorics.pointing-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.universe-levels

open import univalent-combinatorics.species-of-types
```

</details>

## Idea

A pointing of a species of types `F` is the species of types `F*` given by
`F* X := X × (F X)`. In other words, it is the species of pointed `F`-structures

## Definition

```agda
pointing-species-types :
  {l1 l2 : Level} → species-types l1 l2 → species-types l1 (l1 ⊔ l2)
pointing-species-types F X = X × F X
```
