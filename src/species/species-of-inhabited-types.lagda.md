# Species of inhabited types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species.species-of-inhabited-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-types funext univalence truncations
open import foundation.unit-type
open import foundation.universe-levels

open import species.species-of-types-in-subuniverses funext univalence
```

</details>

## Idea

A **species of inhabited types** is a map from the subuniverse of inhabited
types to a universe.

## Definition

```agda
species-inhabited-types : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-inhabited-types l1 l2 =
  species-subuniverse (is-inhabited-Prop {l1}) λ (X : UU l2) → unit-Prop
```
