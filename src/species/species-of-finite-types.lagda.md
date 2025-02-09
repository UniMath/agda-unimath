# Species of finite types

```agda
module species.species-of-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import species.species-of-types-in-subuniverses

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **species of finite types** is a map from `Finite-Type` to a `Finite-Type`.

## Definition

```agda
finite-species : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
finite-species l1 l2 =
  species-subuniverse (is-finite-Prop {l1}) (is-finite-Prop {l2})
```
