# Finite species

```agda
module univalent-combinatorics.finite-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

</details>

### Idea

In this file, we define the type of finite species. A finite
species is just a map from 𝔽 to 𝔽.

## Definition

```agda
finite-species : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
finite-species l1 l2 = 𝔽 l1 → 𝔽 l2

species-finite-species : {l1 l2 : Level} → finite-species l1 l2 → species l1 l2
species-finite-species F X = type-𝔽 (F X)
```
