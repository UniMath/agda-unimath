# Species of types

```agda
module species.species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.equivalences
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels
```

</details>

### Idea

A **species of types** is defined to be a map from a universe to a universe.

## Definitions

### Species of types

```agda
species-types : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-types l1 l2 = UU l1 → UU l2
```

### The predicate that a species preserves cartesian products

```agda
preserves-product-species-types :
  {l1 l2 : Level}
  (S : species-types l1 l2) →
  UU (lsuc l1 ⊔ l2)
preserves-product-species-types {l1} S = (X Y : UU l1) → S (X × Y) ≃ (S X × S Y)
```

### Transport in species

```agda
tr-species-types :
  {l1 l2 : Level} (F : species-types l1 l2) (X Y : UU l1) →
  X ≃ Y → F X → F Y
tr-species-types F X Y e = tr F (eq-equiv e)
```
