# Conjunction of propositions

```agda
module foundation.conjunction-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

The
{{#concept "conjunction" Disambiguation="of propositions" Agda=conjunction-Prop}}
of two [propositions](foundation-core.propositions.md) `P` and `Q` is the
proposition that both `P` and `Q` hold. Although the product of two propositions
is again a proposition, we define the conjunction of two propositions to be the
[conjunction](foundation.conjunction.md) of their underlying types. This means
that it is defined as the
[propositional truncation](foundation.propositional-truncations.md) of the
product of the underlying types of `P` and `Q`.

## Definition

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  conjunction-Prop : Prop (l1 ⊔ l2)
  conjunction-Prop = conjunction-prop (type-Prop P) (type-Prop Q)

  type-conjunction-Prop : UU (l1 ⊔ l2)
  type-conjunction-Prop = type-Prop conjunction-Prop

  is-prop-conjunction-Prop :
    is-prop type-conjunction-Prop
  is-prop-conjunction-Prop = is-prop-type-Prop conjunction-Prop

  infixr 15 _∧₍₋₁₎_
  _∧₍₋₁₎_ : Prop (l1 ⊔ l2)
  _∧₍₋₁₎_ = conjunction-Prop
```

The indexing $-1$ for the infix binary operator `∧₍₋₁₎` is part of a general
scheme, where `∧₍ₙ₎` takes as inputs
$n$-[types](foundation-core.truncated-types.md), and spits out the propositional
conjunction of their underlying types, as an $n$-type. This is in contrast to
the cartesian product `×₍ₙ₎`, which will take values in $n$-types that are not
generally $k$-truncated for any $k < n$.

**Note**: The symbol used for the conjunction `_∧₍₋₁₎_` is the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` or
`\and`).

```agda
module _
  {l1 l2 : Level} (P : Decidable-Prop l1) (Q : Decidable-Prop l2)
  where

  is-decidable-conjunction-Decidable-Prop :
    is-decidable
      ( type-conjunction-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q))
  is-decidable-conjunction-Decidable-Prop =
    is-decidable-trunc-Prop-is-merely-decidable
      ( type-Decidable-Prop P × type-Decidable-Prop Q)
      ( unit-trunc-Prop
        ( is-decidable-product
          ( is-decidable-Decidable-Prop P)
          ( is-decidable-Decidable-Prop Q)))

  conjunction-Decidable-Prop : Decidable-Prop (l1 ⊔ l2)
  pr1 conjunction-Decidable-Prop =
    type-conjunction-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)
  pr1 (pr2 conjunction-Decidable-Prop) =
    is-prop-conjunction-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q)
  pr2 (pr2 conjunction-Decidable-Prop) =
    is-decidable-conjunction-Decidable-Prop
```

### The introduction rule for the conjunction of propositions

```agda
intro-conjunction-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  type-Prop P → type-Prop Q → type-conjunction-Prop P Q
intro-conjunction-Prop P Q = intro-conjunction
```

### The projections for the conjunction of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  pr1-conjunction-Prop : type-conjunction-Prop P Q → type-Prop P
  pr1-conjunction-Prop = rec-trunc-Prop P pr1

  pr2-conjunction-Prop : type-conjunction-Prop P Q → type-Prop Q
  pr2-conjunction-Prop = rec-trunc-Prop Q pr2
```

### The universal property of the conjunction of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  prop-ev-conjunction-Prop : {l : Level} (R : Prop l) → Prop (l1 ⊔ l2 ⊔ l)
  prop-ev-conjunction-Prop R =
    ((P ∧₍₋₁₎ Q) →₍₋₁₎ R) →₍₋₁₎ P →₍₋₁₎ Q →₍₋₁₎ R

  ev-conjunction-Prop :
    {l : Level} (R : Prop l) → type-Prop (prop-ev-conjunction-Prop R)
  ev-conjunction-Prop R f a b = f (intro-conjunction a b)

  universal-property-conjunction-Prop : UUω
  universal-property-conjunction-Prop =
    {l : Level} (R : Prop l) → is-equiv (ev-conjunction-Prop R)
```

## Properties

### The conjunction of propositions satisfies the universal property of the conjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  prop-rec-conjunction-Prop : {l : Level} (R : Prop l) → Prop (l1 ⊔ l2 ⊔ l)
  prop-rec-conjunction-Prop R =
    (P →₍₋₁₎ Q →₍₋₁₎ R) →₍₋₁₎ (P ∧₍₋₁₎ Q) →₍₋₁₎ R

  rec-conjunction-Prop :
    {l : Level} (R : Prop l) → type-Prop (prop-rec-conjunction-Prop R)
  rec-conjunction-Prop = rec-conjunction (type-Prop P) (type-Prop Q)

  up-conjunction-Prop : universal-property-conjunction-Prop P Q
  up-conjunction-Prop = up-conjunction (type-Prop P) (type-Prop Q)

  equiv-ev-conjunction-Prop :
    {l : Level} (R : Prop l) →
    (type-Prop P ∧ type-Prop Q → type-Prop R) ≃
    (type-Prop P → type-Prop Q → type-Prop R)
  equiv-ev-conjunction-Prop = equiv-ev-conjunction (type-Prop P) (type-Prop Q)
```

### The conjuntion of propositions is equivalent to the product of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  map-product-conjunction-Prop :
    type-conjunction-Prop P Q → type-product-Prop P Q
  map-product-conjunction-Prop = rec-trunc-Prop (product-Prop P Q) id

  map-conjunction-product-Prop :
    type-product-Prop P Q → type-conjunction-Prop P Q
  map-conjunction-product-Prop = unit-trunc-Prop

  equiv-conjunction-product-Prop :
    type-product-Prop P Q ≃ type-conjunction-Prop P Q
  equiv-conjunction-product-Prop = equiv-unit-trunc-Prop (product-Prop P Q)

  equiv-product-conjunction-Prop :
    type-conjunction-Prop P Q ≃ type-product-Prop P Q
  equiv-product-conjunction-Prop = inv-equiv equiv-conjunction-product-Prop
```

### The conjuntion of propositions distributes over function types

```agda
module _
  {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (C : UU l3)
  where

  map-distributive-conjunction-Prop :
    type-conjunction-Prop (function-Prop C P) (function-Prop C Q) →
    (C → type-conjunction-Prop P Q)
  map-distributive-conjunction-Prop =
    map-distributive-conjunction (type-Prop P) (type-Prop Q) C

  map-inv-distributive-conjunction-Prop :
    (C → type-conjunction-Prop P Q) →
    type-conjunction-Prop (function-Prop C P) (function-Prop C Q)
  map-inv-distributive-conjunction-Prop f =
    unit-trunc-Prop
      ( pr1-conjunction-Prop P Q ∘ f , pr2-conjunction-Prop P Q ∘ f)

  is-equiv-map-distributive-conjunction-Prop :
    is-equiv map-distributive-conjunction-Prop
  is-equiv-map-distributive-conjunction-Prop =
    is-equiv-is-prop
      ( is-prop-conjunction-Prop (function-Prop C P) (function-Prop C Q))
      ( is-prop-function-Prop (conjunction-Prop P Q))
      ( map-inv-distributive-conjunction-Prop)

  iff-distributive-conjunction-Prop :
    type-conjunction-Prop (function-Prop C P) (function-Prop C Q) ↔
    (C → type-conjunction-Prop P Q)
  iff-distributive-conjunction-Prop =
    ( map-distributive-conjunction-Prop , map-inv-distributive-conjunction-Prop)

  distributive-conjunction-Prop :
    type-conjunction-Prop (function-Prop C P) (function-Prop C Q) ≃
    (C → type-conjunction-Prop P Q)
  distributive-conjunction-Prop =
    ( map-distributive-conjunction-Prop ,
      is-equiv-map-distributive-conjunction-Prop)
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
