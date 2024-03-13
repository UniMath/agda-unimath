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
{{#concept "conjunction" Disambiguation="of propositions" WDID=Q191081 Agda=conjunction-Prop}}
`P ∧ Q` of two [propositions](foundation-core.propositions.md) `P` and `Q` is
the proposition that both `P` and `Q` hold and thus defined by the
[cartesian product](foundation-core.cartesian-product-types.md) of their
underlying types

```text
  P ∧ Q := P × Q
```

The conjunction of two propositions satisfies the universal property of the
[meet](order-theory.greatest-lower-bounds-large-posets.md) in the
[poset of propositions](foundation.large-locale-of-propositions.md). This means
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

$$
(R → P) ∧ (R → Q) ↔ (R → P ∧ Q)
$$

for every proposition `R`. In fact, `R` can be any type.

The
{{#concept "recursion principle" Disambiguation"of the conjunction of propositions" Agda=recursion-principle-conjunction-Prop}}
of the conjunction of propositions states that to define a function `P ∧ Q → R`
into a proposition `R`, or indeed any type, is equivalent to defining a function
`P → Q → R`.

## Definition

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

  infixr 15 _∧₍₋₁₎_
  _∧₍₋₁₎_ : Prop (l1 ⊔ l2)
  _∧₍₋₁₎_ = conjunction-Prop
```

The indexing $-1$ for the infix binary operator `∧₍₋₁₎` is part of a general
scheme, because `∧₍₋₁₎` takes as inputs
$-1$-[types](foundation-core.truncated-types.md), and spits out the
propositional conjunction of their underlying types, as a $-1$-type. This is in
contrast to the cartesian product `×₍ₙ₎`, which will take values in $n$-types
that are not generally $k$-truncated for any $k < n$.

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
    is-decidable-product
      ( is-decidable-Decidable-Prop P)
      ( is-decidable-Decidable-Prop Q)

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
intro-conjunction-Prop P Q = pair
```

### The projections for the conjunction of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  pr1-conjunction-Prop : type-conjunction-Prop P Q → type-Prop P
  pr1-conjunction-Prop = pr1

  pr2-conjunction-Prop : type-conjunction-Prop P Q → type-Prop Q
  pr2-conjunction-Prop = pr2
```

### The recursion principle of the conjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  prop-recursion-principle-conjunction-Prop :
    {l : Level} (R : Prop l) → Prop (l1 ⊔ l2 ⊔ l)
  prop-recursion-principle-conjunction-Prop R =
    ((P ∧₍₋₁₎ Q) →₍₋₁₎ R) ↔₍₋₁₎ (P →₍₋₁₎ Q →₍₋₁₎ R)

  recursion-principle-conjunction-Prop : UUω
  recursion-principle-conjunction-Prop =
    {l : Level} (R : Prop l) →
    type-Prop (prop-recursion-principle-conjunction-Prop R)

  ev-conjunction-Prop :
    {l : Level} (R : Prop l) →
    type-Prop (((P ∧₍₋₁₎ Q) →₍₋₁₎ R) →₍₋₁₎ P →₍₋₁₎ Q →₍₋₁₎ R)
  ev-conjunction-Prop R = ev-pair
```

## Properties

### The conjunction satisfies the recursion principle of the conjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  prop-rec-conjunction-Prop : {l : Level} (R : Prop l) → Prop (l1 ⊔ l2 ⊔ l)
  prop-rec-conjunction-Prop R =
    (P →₍₋₁₎ Q →₍₋₁₎ R) →₍₋₁₎ (P ∧₍₋₁₎ Q) →₍₋₁₎ R

  rec-conjunction-Prop :
    {l : Level} (R : Prop l) → type-Prop (prop-rec-conjunction-Prop R)
  rec-conjunction-Prop R f (p , q) = f p q

  up-conjunction-Prop : recursion-principle-conjunction-Prop P Q
  up-conjunction-Prop R = ev-conjunction-Prop P Q R , rec-conjunction-Prop R

  equiv-ev-conjunction-Prop :
    {l : Level} (R : Prop l) →
    type-Prop (P ∧₍₋₁₎ Q →₍₋₁₎ R) ≃
    type-Prop (P →₍₋₁₎ Q →₍₋₁₎ R)
  equiv-ev-conjunction-Prop R =
    equiv-iff'
      ( P ∧₍₋₁₎ Q →₍₋₁₎ R)
      ( P →₍₋₁₎ Q →₍₋₁₎ R)
      ( up-conjunction-Prop R)
```

### The conjunction is the meet in the poset of propositions

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
  map-inv-distributive-conjunction-Prop f =
      ( pr1-conjunction-Prop P Q ∘ f , pr2-conjunction-Prop P Q ∘ f)

  is-equiv-map-distributive-conjunction-Prop :
    is-equiv map-distributive-conjunction-Prop
  is-equiv-map-distributive-conjunction-Prop =
    is-equiv-Prop'
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

  is-greatest-lower-bound-conjunction-Prop :
    type-Prop ((R →₍₋₁₎ P) ∧₍₋₁₎ (R →₍₋₁₎ Q)) ↔
    type-Prop (R →₍₋₁₎ P ∧₍₋₁₎ Q)
  is-greatest-lower-bound-conjunction-Prop =
    ( map-distributive-conjunction-Prop P Q (type-Prop R) ,
      map-inv-distributive-conjunction-Prop P Q (type-Prop R))
```

## See also

- The indexed analogue of conjunction is
  [universal quantification](foundation.universal-quantification).

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [logical conjunction](https://ncatlab.org/nlab/show/logical+conjunction) at
  $n$Lab
- [Logical conjunction](https://en.wikipedia.org/wiki/Logical_conjunction) at
  Wikipedia
