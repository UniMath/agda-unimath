# Species of finite inhabited types

```agda
module species.species-of-finite-inhabited-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import species.species-of-types-in-subuniverses

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

A **species of finite inhabited types** is a map from the subuniverse of finite
inhabited types to a universe of finite types.

## Definition

```agda
species-Inhabited-Finite-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-Inhabited-Finite-Type l1 l2 =
  species-subuniverse (is-finite-and-inhabited-Prop {l1}) (is-finite-Prop {l2})
```
