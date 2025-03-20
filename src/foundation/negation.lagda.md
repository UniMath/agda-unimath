# Negation

```agda
open import foundation.function-extensionality-axiom

module
  foundation.negation
  (funext : function-extensionality)
  where

open import foundation-core.negation public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.logical-equivalences funext
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

The
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of negation in type theory is the interpretation of the proposition `P ⇒ ⊥`
using propositions as types. Thus, the negation of a type `A` is the type
`A → empty`.

## Properties

### The negation of a type is a proposition

```agda
is-prop-neg : {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg = is-prop-function-type is-prop-empty

neg-type-Prop : {l1 : Level} → UU l1 → Prop l1
neg-type-Prop A = ¬ A , is-prop-neg

neg-Prop : {l1 : Level} → Prop l1 → Prop l1
neg-Prop P = neg-type-Prop (type-Prop P)

type-neg-Prop : {l1 : Level} → Prop l1 → UU l1
type-neg-Prop P = type-Prop (neg-Prop P)

infix 25 ¬'_

¬'_ : {l1 : Level} → Prop l1 → Prop l1
¬'_ = neg-Prop

eq-neg : {l : Level} {A : UU l} {p q : ¬ A} → p ＝ q
eq-neg = eq-is-prop is-prop-neg
```

### Logically equivalent types have logically equivalent negations

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  iff-neg : X ↔ Y → ¬ X ↔ ¬ Y
  iff-neg e = map-neg (backward-implication e) , map-neg (forward-implication e)

  equiv-iff-neg : X ↔ Y → ¬ X ≃ ¬ Y
  equiv-iff-neg e =
    equiv-iff' (neg-type-Prop X) (neg-type-Prop Y) (iff-neg e)
```

### Equivalent types have equivalent negations

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  equiv-neg : X ≃ Y → ¬ X ≃ ¬ Y
  equiv-neg e = equiv-iff-neg (iff-equiv e)
```

### Negation has no fixed points

```agda
abstract
  no-fixed-points-neg-Prop :
    {l : Level} (P : Prop l) → ¬ (type-Prop P ↔ ¬ (type-Prop P))
  no-fixed-points-neg-Prop P = no-fixed-points-neg (type-Prop P)
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [negation](https://ncatlab.org/nlab/show/negation) at $n$Lab
- [Negation](https://en.wikipedia.org/wiki/Negation) at Wikipedia
