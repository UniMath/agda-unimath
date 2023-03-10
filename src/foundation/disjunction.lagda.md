# Disjunction of propositions

```agda
module foundation.disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.propositional-truncations

open import foundation-core.decidable-propositions
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.propositions
open import foundation-core.universe-levels
```

</details>

## Idea

The disjunction of two propositions `P` and `Q` is the proposition that `P` holds or `Q` holds.

## Definition

```agda
disj-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
disj-Prop P Q = trunc-Prop (type-Prop P + type-Prop Q)

type-disj-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (l1 ⊔ l2)
type-disj-Prop P Q = type-Prop (disj-Prop P Q)

abstract
  is-prop-type-disj-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-prop (type-disj-Prop P Q)
  is-prop-type-disj-Prop P Q = is-prop-type-Prop (disj-Prop P Q)

disj-decidable-Prop :
  {l1 l2 : Level} → decidable-Prop l1 → decidable-Prop l2 → decidable-Prop (l1 ⊔ l2)
pr1 (disj-decidable-Prop P Q) = type-disj-Prop (prop-decidable-Prop P) (prop-decidable-Prop Q)
pr1 (pr2 (disj-decidable-Prop P Q)) =
  is-prop-type-disj-Prop (prop-decidable-Prop P) (prop-decidable-Prop Q)
pr2 (pr2 (disj-decidable-Prop P Q)) =
  is-decidable-trunc-Prop-is-merely-decidable
    ( type-decidable-Prop P + type-decidable-Prop Q)
    ( unit-trunc-Prop
      ( is-decidable-coprod
        ( is-decidable-type-decidable-Prop P)
        ( is-decidable-type-decidable-Prop Q)))
```

## Properties

### The introduction rules for disjunction

```agda
inl-disj-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  type-hom-Prop P (disj-Prop P Q)
inl-disj-Prop P Q = unit-trunc-Prop ∘ inl

inr-disj-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  type-hom-Prop Q (disj-Prop P Q)
inr-disj-Prop P Q = unit-trunc-Prop ∘ inr
```

### The elimination rule and universal property of disjunction

```agda
ev-disj-Prop :
  {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3) →
  type-hom-Prop
    ( hom-Prop (disj-Prop P Q) R)
    ( conj-Prop (hom-Prop P R) (hom-Prop Q R))
pr1 (ev-disj-Prop P Q R h) = h ∘ (inl-disj-Prop P Q)
pr2 (ev-disj-Prop P Q R h) = h ∘ (inr-disj-Prop P Q)

elim-disj-Prop :
  {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3) →
  type-hom-Prop
    ( conj-Prop (hom-Prop P R) (hom-Prop Q R))
    ( hom-Prop (disj-Prop P Q) R)
elim-disj-Prop P Q R (pair f g) =
  map-universal-property-trunc-Prop R (ind-coprod (λ t → type-Prop R) f g)

abstract
  is-equiv-ev-disj-Prop :
    {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3) →
    is-equiv (ev-disj-Prop P Q R)
  is-equiv-ev-disj-Prop P Q R =
    is-equiv-is-prop
      ( is-prop-type-Prop (hom-Prop (disj-Prop P Q) R))
      ( is-prop-type-Prop (conj-Prop (hom-Prop P R) (hom-Prop Q R)))
      ( elim-disj-Prop P Q R)
```
