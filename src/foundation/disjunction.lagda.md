# Disjunction of propositions

```agda
module foundation.disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

The disjunction of two propositions `P` and `Q` is the proposition that `P`
holds or `Q` holds.

## Definition

```agda
disj-Prop : {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
disj-Prop P Q = trunc-Prop (type-Prop P + type-Prop Q)

_∨_ = disj-Prop
```

**Note**: The symbol used for the disjunction `_∨_` is the
[logical or](https://codepoints.net/U+2228) `∨` (agda-input: `\vee` `\or`), and
not the [latin small letter v](https://codepoints.net/U+0076) `v`.

```agda
type-disj-Prop : {l1 l2 : Level} → Prop l1 → Prop l2 → UU (l1 ⊔ l2)
type-disj-Prop P Q = type-Prop (disj-Prop P Q)

abstract
  is-prop-type-disj-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-prop (type-disj-Prop P Q)
  is-prop-type-disj-Prop P Q = is-prop-type-Prop (disj-Prop P Q)

disj-Decidable-Prop :
  {l1 l2 : Level} →
  Decidable-Prop l1 → Decidable-Prop l2 → Decidable-Prop (l1 ⊔ l2)
pr1 (disj-Decidable-Prop P Q) =
  type-disj-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)
pr1 (pr2 (disj-Decidable-Prop P Q)) =
  is-prop-type-disj-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)
pr2 (pr2 (disj-Decidable-Prop P Q)) =
  is-decidable-trunc-Prop-is-merely-decidable
    ( type-Decidable-Prop P + type-Decidable-Prop Q)
    ( unit-trunc-Prop
      ( is-decidable-coprod
        ( is-decidable-Decidable-Prop P)
        ( is-decidable-Decidable-Prop Q)))
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
