# Species of finite inhabited types

```agda
module species.species-of-finite-inhabited-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import species.species-of-types-in-subuniverse

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

A species of finite inhabited type is a map from the subuniverse of inhabited
finite types to a `𝔽`.

## Definition

```agda
species-Inhabited-Type-𝔽 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-Inhabited-Type-𝔽 l1 l2 =
  species-subuniverse (is-finite-and-inhabited-Prop {l1}) (is-finite-Prop {l2})
```
