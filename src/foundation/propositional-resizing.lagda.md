# Propositional resizing

```agda
module foundation.propositional-resizing where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences-propositions
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.propositions
open import foundation-core.small-types
open import foundation-core.subtypes
```

</details>

## Idea

We say that a universe `𝒱` satisfies `𝒰`-small
{{#concept "propositional resizing" Agda=propositional-resizing-Level}} if there
is a type `Ω` in `𝒰` [equipped](foundation.structure.md) with a
[subtype](foundation-core.subtypes.md) `Q` such that for each proposition `P` in
`𝒱` there is an element `u : Ω` such that `Q u ≃ P`. Such a type `Ω` is called
an `𝒰`-small {{#concept "classifier" Disambiguation="of small subobjects"}} of
`𝒱`-small subobjects.

## Definitions

### The predicate on a type of being a subtype classifier of a given universe level

```agda
is-subtype-classifier :
  {l1 l2 : Level} (l3 : Level) → Σ (UU l1) (subtype l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
is-subtype-classifier l3 Ω =
  (P : Prop l3) → Σ (pr1 Ω) (λ u → type-equiv-Prop P (pr2 Ω u))

module _
  {l1 l2 l3 : Level}
  (Ω : Σ (UU l1) (subtype l2)) (H : is-subtype-classifier l3 Ω)
  (P : Prop l3)
  where

  object-prop-is-subtype-classifier : pr1 Ω
  object-prop-is-subtype-classifier = pr1 (H P)

  prop-is-small-prop-is-subtype-classifier : Prop l2
  prop-is-small-prop-is-subtype-classifier =
    pr2 Ω object-prop-is-subtype-classifier

  type-is-small-prop-is-subtype-classifier : UU l2
  type-is-small-prop-is-subtype-classifier =
    type-Prop prop-is-small-prop-is-subtype-classifier

  equiv-is-small-prop-is-subtype-classifier :
    type-Prop P ≃ type-is-small-prop-is-subtype-classifier
  equiv-is-small-prop-is-subtype-classifier = pr2 (H P)

  is-small-prop-is-subtype-classifier : is-small l2 (type-Prop P)
  is-small-prop-is-subtype-classifier =
    ( type-is-small-prop-is-subtype-classifier ,
      equiv-is-small-prop-is-subtype-classifier)
```

### Propositional resizing between specified universes

```agda
propositional-resizing-Level' :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
propositional-resizing-Level' l1 l2 l3 =
  Σ (Σ (UU l1) (subtype l2)) (is-subtype-classifier l3)

propositional-resizing-Level :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
propositional-resizing-Level l1 l2 =
  propositional-resizing-Level' l1 l1 l2
```

```agda
module _
  {l1 l2 l3 : Level} (ρ : propositional-resizing-Level' l1 l2 l3)
  where

  subtype-classifier-propositional-resizing-Level : Σ (UU l1) (subtype l2)
  subtype-classifier-propositional-resizing-Level = pr1 ρ

  type-subtype-classifier-propositional-resizing-Level : UU l1
  type-subtype-classifier-propositional-resizing-Level =
    pr1 subtype-classifier-propositional-resizing-Level

  is-subtype-classifier-subtype-classifier-propositional-resizing-Level :
    is-subtype-classifier l3 subtype-classifier-propositional-resizing-Level
  is-subtype-classifier-subtype-classifier-propositional-resizing-Level = pr2 ρ

module _
  {l1 l2 l3 : Level} (ρ : propositional-resizing-Level' l1 l2 l3) (P : Prop l3)
  where

  object-prop-propositional-resizing-Level :
    type-subtype-classifier-propositional-resizing-Level ρ
  object-prop-propositional-resizing-Level =
    object-prop-is-subtype-classifier
      ( subtype-classifier-propositional-resizing-Level ρ)
      ( is-subtype-classifier-subtype-classifier-propositional-resizing-Level ρ)
      ( P)

  prop-is-small-prop-propositional-resizing-Level : Prop l2
  prop-is-small-prop-propositional-resizing-Level =
    prop-is-small-prop-is-subtype-classifier
      ( subtype-classifier-propositional-resizing-Level ρ)
      ( is-subtype-classifier-subtype-classifier-propositional-resizing-Level ρ)
      ( P)

  type-is-small-prop-propositional-resizing-Level : UU l2
  type-is-small-prop-propositional-resizing-Level =
    type-is-small-prop-is-subtype-classifier
      ( subtype-classifier-propositional-resizing-Level ρ)
      ( is-subtype-classifier-subtype-classifier-propositional-resizing-Level ρ)
      ( P)

  equiv-is-small-prop-propositional-resizing-Level :
    type-Prop P ≃ type-is-small-prop-propositional-resizing-Level
  equiv-is-small-prop-propositional-resizing-Level =
    equiv-is-small-prop-is-subtype-classifier
      ( subtype-classifier-propositional-resizing-Level ρ)
      ( is-subtype-classifier-subtype-classifier-propositional-resizing-Level ρ)
      ( P)

  is-small-prop-propositional-resizing-Level : is-small l2 (type-Prop P)
  is-small-prop-propositional-resizing-Level =
    is-small-prop-is-subtype-classifier
      ( subtype-classifier-propositional-resizing-Level ρ)
      ( is-subtype-classifier-subtype-classifier-propositional-resizing-Level ρ)
      ( P)
```

### The propositional resizing axiom

```agda
propositional-resizing : UUω
propositional-resizing = (l1 l2 : Level) → propositional-resizing-Level l1 l2
```

```agda
module _
  (ρ : propositional-resizing) (l1 l2 : Level)
  where

  subtype-classifier-propositional-resizing : Σ (UU l1) (subtype l1)
  subtype-classifier-propositional-resizing = pr1 (ρ l1 l2)

  type-subtype-classifier-propositional-resizing : UU l1
  type-subtype-classifier-propositional-resizing =
    type-subtype-classifier-propositional-resizing-Level (ρ l1 l2)

  is-subtype-classifier-subtype-classifier-propositional-resizing :
    is-subtype-classifier l2 subtype-classifier-propositional-resizing
  is-subtype-classifier-subtype-classifier-propositional-resizing =
    is-subtype-classifier-subtype-classifier-propositional-resizing-Level
      ( ρ l1 l2)

module _
  (ρ : propositional-resizing) (l1 : Level) {l2 : Level} (P : Prop l2)
  where

  object-prop-propositional-resizing :
    type-subtype-classifier-propositional-resizing ρ l1 l2
  object-prop-propositional-resizing =
    object-prop-propositional-resizing-Level (ρ l1 l2) P

  prop-is-small-prop-propositional-resizing : Prop l1
  prop-is-small-prop-propositional-resizing =
    prop-is-small-prop-propositional-resizing-Level (ρ l1 l2) P

  type-is-small-prop-propositional-resizing : UU l1
  type-is-small-prop-propositional-resizing =
    type-is-small-prop-propositional-resizing-Level (ρ l1 l2) P

  equiv-is-small-prop-propositional-resizing :
    type-Prop P ≃ type-is-small-prop-propositional-resizing
  equiv-is-small-prop-propositional-resizing =
    equiv-is-small-prop-propositional-resizing-Level (ρ l1 l2) P

  is-small-prop-propositional-resizing : is-small l1 (type-Prop P)
  is-small-prop-propositional-resizing =
    is-small-prop-propositional-resizing-Level (ρ l1 l2) P
```

## See also

- [The large locale of propositions](foundation.large-locale-of-propositions.md)

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
