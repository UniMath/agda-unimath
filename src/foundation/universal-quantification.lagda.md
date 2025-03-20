# Universal quantification

```agda
open import foundation.function-extensionality-axiom

module
  foundation.universal-quantification
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.evaluation-functions
open import foundation.logical-equivalences funext
open import foundation.propositional-truncations funext
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

Given a type `A` and a [subtype](foundation-core.subtypes.md) `P : A → Prop`,
the
{{#concept "universal quantification" Disambiguation="on a subtype" WDID=Q126695 WD="universal quantification"}}

```text
  ∀ (x : A), (P x)
```

is the [proposition](foundation-core.propositions.md) that there exists a proof
of `P x` for every `x` in `A`.

The
{{#concept "universal property" Disambiguation="of universal quantification" Agda=universal-property-for-all}}
of universal quantification states that it is the
[greatest lower bound](order-theory.greatest-lower-bounds-large-posets.md) on
the family of propositions `P` in the
[locale of propositions](foundation.large-locale-of-propositions.md), by which
we mean that for every proposition `Q` we have the
[logical equivalence](foundation.logical-equivalences.md)

```text
  (∀ (a : A), (R → P a)) ↔ (R → ∀ (a : A), (P a))
```

**Notation.** Because of syntactic limitations of the Agda language, we cannot
use `∀` for the universal quantification in formalizations, and instead use
`∀'`.

## Definitions

### Universal quantification

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  for-all-Prop : Prop (l1 ⊔ l2)
  for-all-Prop = Π-Prop A P

  type-for-all-Prop : UU (l1 ⊔ l2)
  type-for-all-Prop = type-Prop for-all-Prop

  is-prop-for-all-Prop : is-prop type-for-all-Prop
  is-prop-for-all-Prop = is-prop-type-Prop for-all-Prop

  for-all : UU (l1 ⊔ l2)
  for-all = type-for-all-Prop

  ∀' : Prop (l1 ⊔ l2)
  ∀' = for-all-Prop
```

### The universal property of universal quantification

The
{{#concept "universal property" Disambiguation="of universal quantification" Agda=universal-property-for-all}}
of the universal quantification `∀ (a : A), (P a)` states that for every
proposition `R`, the canonical map

```text
  (∀ (a : A), (R → P a)) → (R → ∀ (a : A), (P a))
```

is a [logical equivalence](foundation.logical-equivalences.md). Indeed, this
holds for any type `R`.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  universal-property-for-all : {l3 : Level} (S : Prop l3) → UUω
  universal-property-for-all S =
    {l : Level} (R : Prop l) →
    type-Prop ((∀' A (λ a → R ⇒ P a)) ⇔ (R ⇒ S))

  ev-for-all :
    {l : Level} {B : UU l} →
    for-all A (λ a → function-Prop B (P a)) → B → for-all A P
  ev-for-all f r a = f a r
```

## Properties

### Universal quantification satisfies its universal property

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  map-up-for-all :
    {l : Level} {B : UU l} →
    (B → for-all A P) → for-all A (λ a → function-Prop B (P a))
  map-up-for-all f a r = f r a

  is-equiv-ev-for-all :
    {l : Level} {B : UU l} → is-equiv (ev-for-all A P {B = B})
  is-equiv-ev-for-all {B = B} =
    is-equiv-has-converse
      ( ∀' A (λ a → function-Prop B (P a)))
      ( function-Prop B (∀' A P))
      ( map-up-for-all)

  up-for-all : universal-property-for-all A P (∀' A P)
  up-for-all R = (ev-for-all A P , map-up-for-all)
```

## See also

- Universal quantification is the indexed counterpart to
  [conjunction](foundation.conjunction.md).

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [universal quantifier](https://ncatlab.org/nlab/show/universal+quantifier) at
  $n$Lab
- [Universal quantification](https://en.wikipedia.org/wiki/Universal_quantification)
  at Wikipedia
