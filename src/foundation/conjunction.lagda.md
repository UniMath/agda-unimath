# Conjunction

```agda
module foundation.conjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universal-property-cartesian-product-types
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
{{#concept "conjunction" Disambiguation="of propositions" WDID=Q191081 WD="logical conjunction" Agda=conjunction-Prop}}
`P ∧ Q` of two [propositions](foundation-core.propositions.md) `P` and `Q` is
the proposition that both `P` and `Q` hold and is thus defined by the
[cartesian product](foundation-core.cartesian-product-types.md) of their
underlying types

```text
  P ∧ Q := P × Q
```

The conjunction of two propositions satisfies the universal property of the
[meet](order-theory.greatest-lower-bounds-large-posets.md) in the
[locale of propositions](foundation.large-locale-of-propositions.md). This means
that any span of propositions over `P` and `Q` factor (uniquely) through the
conjunction

```text
           R
        /  ∶  \
      /    ∶    \
    ∨      ∨      ∨
  P <--- P ∧ Q ---> Q.
```

In other words, we have a
[logical equivalence](foundation.logical-equivalences.md)

```text
  (R → P) ∧ (R → Q) ↔ (R → P ∧ Q)
```

for every proposition `R`. In fact, `R` can be any type.

The
{{#concept "recursion principle" Disambiguation"of the conjunction of propositions" Agda=elimination-principle-conjunction-Prop}}
of the conjunction of propositions states that to define a function `P ∧ Q → R`
into a proposition `R`, or indeed any type, is equivalent to defining a function
`P → Q → R`.

## Definitions

### The conjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  conjunction-Prop : Prop (l1 ⊔ l2)
  conjunction-Prop = product-Prop P Q

  type-conjunction-Prop : UU (l1 ⊔ l2)
  type-conjunction-Prop = type-Prop conjunction-Prop

  is-prop-conjunction-Prop :
    is-prop type-conjunction-Prop
  is-prop-conjunction-Prop = is-prop-type-Prop conjunction-Prop

  infixr 15 _∧_
  _∧_ : Prop (l1 ⊔ l2)
  _∧_ = conjunction-Prop
```

**Note**: The symbol used for the conjunction `_∧_` is the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` or
`\and`).

### The conjunction of decidable propositions

```agda
module _
  {l1 l2 : Level} (P : Decidable-Prop l1) (Q : Decidable-Prop l2)
  where

  is-decidable-conjunction-Decidable-Prop :
    is-decidable
      ( type-conjunction-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q))
  is-decidable-conjunction-Decidable-Prop =
    is-decidable-product
      ( is-decidable-Decidable-Prop P)
      ( is-decidable-Decidable-Prop Q)

  conjunction-Decidable-Prop : Decidable-Prop (l1 ⊔ l2)
  conjunction-Decidable-Prop =
    ( type-conjunction-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q) ,
      is-prop-conjunction-Prop (prop-Decidable-Prop P) (prop-Decidable-Prop Q) ,
      is-decidable-conjunction-Decidable-Prop)
```

### The introduction rule and projections for the conjunction of propositions

While we define the introduction rule and projections for the conjunction below,
we advice users to use the standard pairing and projection functions for the
cartesian product types: `pair`, `pr1` and `pr2`.

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  intro-conjunction-Prop : type-Prop P → type-Prop Q → type-conjunction-Prop P Q
  intro-conjunction-Prop = pair

  pr1-conjunction-Prop : type-conjunction-Prop P Q → type-Prop P
  pr1-conjunction-Prop = pr1

  pr2-conjunction-Prop : type-conjunction-Prop P Q → type-Prop Q
  pr2-conjunction-Prop = pr2
```

### The elimination principle of the conjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  ev-conjunction-Prop :
    {l : Level} (R : Prop l) → type-Prop (((P ∧ Q) ⇒ R) ⇒ P ⇒ Q ⇒ R)
  ev-conjunction-Prop R = ev-pair

  elimination-principle-conjunction-Prop : UUω
  elimination-principle-conjunction-Prop =
    {l : Level} (R : Prop l) → has-converse (ev-conjunction-Prop R)
```

## Properties

### The conjunction satisfies the recursion principle of the conjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  elim-conjunction-Prop : elimination-principle-conjunction-Prop P Q
  elim-conjunction-Prop R f (p , q) = f p q
```

### The conjunction is the meet in the locale of propositions

```agda
module _
  {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (C : UU l3)
  where

  map-distributive-conjunction-Prop :
    type-conjunction-Prop (function-Prop C P) (function-Prop C Q) →
    C → type-conjunction-Prop P Q
  map-distributive-conjunction-Prop (f , g) y = (f y , g y)

  map-inv-distributive-conjunction-Prop :
    (C → type-conjunction-Prop P Q) →
    type-conjunction-Prop (function-Prop C P) (function-Prop C Q)
  map-inv-distributive-conjunction-Prop f = (pr1 ∘ f , pr2 ∘ f)

  is-equiv-map-distributive-conjunction-Prop :
    is-equiv map-distributive-conjunction-Prop
  is-equiv-map-distributive-conjunction-Prop =
    is-equiv-has-converse
      ( conjunction-Prop (function-Prop C P) (function-Prop C Q))
      ( function-Prop C (conjunction-Prop P Q))
      ( map-inv-distributive-conjunction-Prop)

  distributive-conjunction-Prop :
    type-conjunction-Prop (function-Prop C P) (function-Prop C Q) ≃
    (C → type-conjunction-Prop P Q)
  distributive-conjunction-Prop =
    ( map-distributive-conjunction-Prop ,
      is-equiv-map-distributive-conjunction-Prop)

module _
  {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3)
  where

  is-greatest-binary-lower-bound-conjunction-Prop :
    type-Prop (((R ⇒ P) ∧ (R ⇒ Q)) ⇔ (R ⇒ P ∧ Q))
  is-greatest-binary-lower-bound-conjunction-Prop =
    ( map-distributive-conjunction-Prop P Q (type-Prop R) ,
      map-inv-distributive-conjunction-Prop P Q (type-Prop R))
```

## See also

- The indexed counterpart to conjunction is
  [universal quantification](foundation.universal-quantification.md).

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [logical conjunction](https://ncatlab.org/nlab/show/logical+conjunction) at
  $n$Lab
- [Logical conjunction](https://en.wikipedia.org/wiki/Logical_conjunction) at
  Wikipedia
