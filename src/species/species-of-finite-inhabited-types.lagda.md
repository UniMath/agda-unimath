# Species of finite inhabited types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species.species-of-finite-inhabited-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import species.species-of-types-in-subuniverses funext univalence

open import univalent-combinatorics.finite-types funext univalence truncations
open import univalent-combinatorics.inhabited-finite-types funext univalence truncations
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
