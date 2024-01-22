# Conjunction of propositions

```agda
module foundation.conjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.equivalences
open import foundation-core.propositions
```

</details>

## Idea

The **conjunction** of two [propositions](foundation-core.propositions.md) `P`
and `Q` is the proposition that both `P` and `Q` hold.

## Definition

```agda
conjunction-Prop = prod-Prop

type-conjunction-Prop : {l1 l2 : Level} → Prop l1 → Prop l2 → UU (l1 ⊔ l2)
type-conjunction-Prop P Q = type-Prop (conjunction-Prop P Q)

abstract
  is-prop-type-conjunction-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-prop (type-conjunction-Prop P Q)
  is-prop-type-conjunction-Prop P Q = is-prop-type-Prop (conjunction-Prop P Q)

infixr 15 _∧_
_∧_ = conjunction-Prop
```

**Note**: The symbol used for the conjunction `_∧_` is the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` `\and`).

```agda
conjunction-Decidable-Prop :
  {l1 l2 : Level} → Decidable-Prop l1 → Decidable-Prop l2 →
  Decidable-Prop (l1 ⊔ l2)
pr1 (conjunction-Decidable-Prop P Q) =
  type-conjunction-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)
pr1 (pr2 (conjunction-Decidable-Prop P Q)) =
  is-prop-type-conjunction-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)
pr2 (pr2 (conjunction-Decidable-Prop P Q)) =
  is-decidable-prod
    ( is-decidable-Decidable-Prop P)
    ( is-decidable-Decidable-Prop Q)
```

## Properties

### Introduction rule for conjunction

```agda
intro-conjunction-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  type-Prop P → type-Prop Q → type-conjunction-Prop P Q
pr1 (intro-conjunction-Prop P Q p q) = p
pr2 (intro-conjunction-Prop P Q p q) = q
```

### The universal property of conjunction

```agda
iff-universal-property-conjunction-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  {l3 : Level} (R : Prop l3) →
  ( type-hom-Prop R P × type-hom-Prop R Q) ↔
  ( type-hom-Prop R (conjunction-Prop P Q))
pr1 (pr1 (iff-universal-property-conjunction-Prop P Q R) (f , g) r) = f r
pr2 (pr1 (iff-universal-property-conjunction-Prop P Q R) (f , g) r) = g r
pr1 (pr2 (iff-universal-property-conjunction-Prop P Q R) h) r = pr1 (h r)
pr2 (pr2 (iff-universal-property-conjunction-Prop P Q R) h) r = pr2 (h r)

equiv-universal-property-conjunction-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  {l3 : Level} (R : Prop l3) →
  ( type-hom-Prop R P × type-hom-Prop R Q) ≃
  ( type-hom-Prop R (conjunction-Prop P Q))
equiv-universal-property-conjunction-Prop P Q R =
  equiv-iff'
    ( conjunction-Prop (hom-Prop R P) (hom-Prop R Q))
    ( hom-Prop R (conjunction-Prop P Q))
    ( iff-universal-property-conjunction-Prop P Q R)
```
