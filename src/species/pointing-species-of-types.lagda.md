# Pointing of species of types

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species.pointing-species-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.universe-levels

open import species.species-of-types funext univalence
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
