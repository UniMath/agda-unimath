# Decidable relations on types

```agda
module foundation.decidable-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A decidable (binary) relation on `X` is a binary relation `R` on `X` such that each `R x y` is a decidable proposition

## Definitions

### Decidable relations

```agda
Decidable-Relation : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Decidable-Relation l2 X = X → X → decidable-Prop l2

module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-Relation l2 X)
  where

  relation-Decidable-Relation : X → X → Prop l2
  relation-Decidable-Relation x y = prop-decidable-Prop (R x y)

  type-Decidable-Relation : X → X → UU l2
  type-Decidable-Relation x y = type-decidable-Prop (R x y)

  is-prop-type-Decidable-Relation :
    (x y : X) → is-prop (type-Decidable-Relation x y)
  is-prop-type-Decidable-Relation x y = is-prop-type-decidable-Prop (R x y)

  is-decidable-type-Decidable-Relation :
    (x y : X) → is-decidable (type-Decidable-Relation x y)
  is-decidable-type-Decidable-Relation x y =
    is-decidable-type-decidable-Prop (R x y)
```
