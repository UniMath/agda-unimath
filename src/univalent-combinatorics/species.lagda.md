# Species

```agda
module univalent-combinatorics.species where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

</details>

### Idea

In this file, we define the type of species. A species is just a
map from 𝔽 to a universe.

## Definitions

### Species

```agda
species : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species l1 l2 = 𝔽 l1 → UU l2
```

### Transport in species

```agda
tr-species :
  {l1 l2 : Level} (F : species l1 l2) (X Y : 𝔽 l1) →
  type-𝔽 X ≃ type-𝔽 Y → F X → F Y
tr-species F X Y e = tr F (eq-equiv-𝔽 X Y e)
```
