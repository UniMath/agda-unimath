# Disjunction of propositions

```agda
module foundation.disjunction-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

The
{{#concept "disjunction" Disambiguation="of propositions" Agda=disjunction-Prop}}
of two [propositions](foundation-core.propositions.md) `P` and `Q` is the
proposition that `P` holds or `Q` holds.

The universal property of the disjunction states that, for every proposition
`R`, the evaluation map

```text
  ev : ((P ∨ Q) ⇒ R) ⇒ ((P ⇒ R) ∧ (Q ⇒ R))
```

is an [equivalence](foundation.logical-equivalence.md).

## Definitions

### The disjunction of propositions

```agda
disjunction-Prop : {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
disjunction-Prop P Q = disjunction-prop (type-Prop P) (type-Prop Q)

type-disjunction-Prop : {l1 l2 : Level} → Prop l1 → Prop l2 → UU (l1 ⊔ l2)
type-disjunction-Prop P Q = type-Prop (disjunction-Prop P Q)

abstract
  is-prop-disjunction-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-prop (type-disjunction-Prop P Q)
  is-prop-disjunction-Prop P Q = is-prop-type-Prop (disjunction-Prop P Q)

infixr 10 _∨₍₋₁₎_
_∨₍₋₁₎_ = disjunction-Prop
```

The indexing $-1$ for the infix binary operator `∨₍₋₁₎` is part of a general
scheme, where `∨₍ₙ₎` takes as inputs
$n$-[types](foundation-core.truncated-types.md), and spits out the propositional
disjunction of their underlying types. This is in contrast to the coproduct
`+₍ₙ₎`, which would take values in $n$-types.

**Notation.** The symbol used for the disjunction `_∨₍₋₁₎_` is the
[logical or](https://codepoints.net/U+2228) `∨` (agda-input: `\vee` `\or`), and
not the [latin small letter v](https://codepoints.net/U+0076) `v`.

### The introduction rules for the disjunction of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  inl-disjunction-Prop : type-Prop P → type-disjunction-Prop P Q
  inl-disjunction-Prop = inl-disjunction (type-Prop P) (type-Prop Q)

  inr-disjunction-Prop : type-Prop Q → type-disjunction-Prop P Q
  inr-disjunction-Prop = inr-disjunction (type-Prop P) (type-Prop Q)
```

### The universal property of the disjunction of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  prop-ev-disjunction-Prop : {l3 : Level} (R : Prop l3) → Prop (l1 ⊔ l2 ⊔ l3)
  prop-ev-disjunction-Prop R =
    ((P ∨₍₋₁₎ Q) →₍₋₁₎ R) →₍₋₁₎ ((P →₍₋₁₎ R) ×₍₋₁₎ (Q →₍₋₁₎ R))

  ev-disjunction-Prop :
    {l3 : Level} (R : Prop l3) → type-Prop (prop-ev-disjunction-Prop R)
  ev-disjunction-Prop = ev-disjunction (type-Prop P) (type-Prop Q)

  universal-property-disjunction-Prop : UUω
  universal-property-disjunction-Prop =
    universal-property-disjunction (type-Prop P) (type-Prop Q)
```

### The disjunction of decidable propositions

```agda
module _
  {l1 l2 : Level} (P : Decidable-Prop l1) (Q : Decidable-Prop l2)
  where

  type-disjunction-Decidable-Prop : UU (l1 ⊔ l2)
  type-disjunction-Decidable-Prop =
    type-disjunction-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)

  is-prop-disjunction-Decidable-Prop :
    is-prop type-disjunction-Decidable-Prop
  is-prop-disjunction-Decidable-Prop =
    is-prop-disjunction-Prop
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
  disjunction-Decidable-Prop =
    ( type-disjunction-Decidable-Prop ,
      is-prop-disjunction-Decidable-Prop ,
      is-decidable-type-disjunction-Decidable-Prop)
```

## Properties

### The universal property of disjunction of propositions

```agda
abstract
  up-disjunction-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    universal-property-disjunction-Prop P Q
  up-disjunction-Prop P Q =
    up-disjunction (type-Prop P) (type-Prop Q)
```

### The recursion principle of disjunctions of propositions

```agda
module _
  {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3)
  where

  prop-rec-disjunction-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  prop-rec-disjunction-Prop =
    (P →₍₋₁₎ R) →₍₋₁₎ (Q →₍₋₁₎ R) →₍₋₁₎ ((P ∨₍₋₁₎ Q) →₍₋₁₎ R)

  rec-disjunction-Prop :
    type-Prop prop-rec-disjunction-Prop
  rec-disjunction-Prop = rec-disjunction (type-Prop P) (type-Prop Q) R
```

### The unit laws for the disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  map-left-unit-law-disjunction-is-empty-Prop :
    is-empty (type-Prop P) → type-disjunction-Prop P Q → type-Prop Q
  map-left-unit-law-disjunction-is-empty-Prop f =
    rec-disjunction-Prop P Q Q (ex-falso ∘ f) id

  map-right-unit-law-disjunction-is-empty-Prop :
    is-empty (type-Prop Q) → type-disjunction-Prop P Q → type-Prop P
  map-right-unit-law-disjunction-is-empty-Prop f =
    rec-disjunction-Prop P Q P id (ex-falso ∘ f)
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
