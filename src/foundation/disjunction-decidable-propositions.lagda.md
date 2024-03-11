# Disjunction of decidable propositions

```agda
module foundation.disjunction-decidable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.propositions
```

</details>

## Definitions

### Disjunction on decidable propositions

```agda
module _
  {l1 l2 : Level} (P : Decidable-Prop l1) (Q : Decidable-Prop l2)
  where

  type-disjunction-Decidable-Prop : UU (l1 ⊔ l2)
  type-disjunction-Decidable-Prop =
    type-disjunction-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)

  is-prop-type-disjunction-Decidable-Prop :
    is-prop type-disjunction-Decidable-Prop
  is-prop-type-disjunction-Decidable-Prop =
    is-prop-type-disjunction-Prop
      ( prop-Decidable-Prop P)
      ( prop-Decidable-Prop Q)

  is-decidable-type-disjunction-Decidable-Prop :
    is-decidable type-disjunction-Decidable-Prop
  is-decidable-type-disjunction-Decidable-Prop =
    is-decidable-trunc-Prop-is-merely-decidable
      ( type-Decidable-Prop P + type-Decidable-Prop Q)
      ( unit-trunc-Prop
        ( is-decidable-coproduct
          ( is-decidable-Decidable-Prop P)
          ( is-decidable-Decidable-Prop Q)))

  disjunction-Decidable-Prop : Decidable-Prop (l1 ⊔ l2)
  pr1 disjunction-Decidable-Prop =
    type-disjunction-Decidable-Prop
  pr1 (pr2 disjunction-Decidable-Prop) =
    is-prop-type-disjunction-Decidable-Prop
  pr2 (pr2 disjunction-Decidable-Prop) =
    is-decidable-type-disjunction-Decidable-Prop
```
