# Conjunction of propositions

```agda
module foundation.conjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.decidable-propositions
```

</details>

## Idea

The conjunction of two propositions `P` and `Q` is the proposition that both `P` and `Q` hold.

## Definition

```agda
conj-Prop = prod-Prop

type-conj-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (l1 ⊔ l2)
type-conj-Prop P Q = type-Prop (conj-Prop P Q)

abstract
  is-prop-type-conj-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-prop (type-conj-Prop P Q)
  is-prop-type-conj-Prop P Q = is-prop-type-Prop (conj-Prop P Q)

conj-decidable-Prop :
  {l1 l2 : Level} → decidable-Prop l1 → decidable-Prop l2 →
  decidable-Prop (l1 ⊔ l2)
pr1 (conj-decidable-Prop P Q) =
  type-conj-Prop (prop-decidable-Prop P) (prop-decidable-Prop Q)
pr1 (pr2 (conj-decidable-Prop P Q)) =
  is-prop-type-conj-Prop (prop-decidable-Prop P) (prop-decidable-Prop Q)
pr2 (pr2 (conj-decidable-Prop P Q)) =
  is-decidable-prod (is-decidable-type-decidable-Prop P) (is-decidable-type-decidable-Prop Q)
```

## Properties

### Introduction rule for conjunction

```
intro-conj-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  type-Prop P → type-Prop Q → type-conj-Prop P Q
pr1 (intro-conj-Prop P Q p q) = p
pr2 (intro-conj-Prop P Q p q) = q
```
