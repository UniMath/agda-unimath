# Negation

```agda
module foundation.negation where

open import foundation-core.negation public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.propositions
```

</details>

## Idea

The Curry-Howard interpretation of negation in type theory is the interpretation
of the proposition `P ⇒ ⊥` using propositions as types. Thus, the negation of a
type `A` is the type `A → empty`.

## Properties

### The negation of a type is a proposition

```agda
is-prop-neg : {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg {A = A} = is-prop-function-type is-prop-empty

neg-type-Prop : {l1 : Level} → UU l1 → Prop l1
neg-type-Prop A = ¬ A , is-prop-neg

neg-Prop : {l1 : Level} → Prop l1 → Prop l1
neg-Prop P = neg-type-Prop (type-Prop P)

type-neg-Prop : {l1 : Level} → Prop l1 → UU l1
type-neg-Prop P = type-Prop (neg-Prop P)

infix 25 ¬'_

¬'_ : {l1 : Level} → Prop l1 → Prop l1
¬'_ = neg-Prop
```

### Reductio ad absurdum

```agda
reductio-ad-absurdum : {l1 l2 : Level} {P : UU l1} {Q : UU l2} → P → ¬ P → Q
reductio-ad-absurdum p np = ex-falso (np p)
```

### Equivalent types have equivalent negations

```agda
equiv-neg :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  (X ≃ Y) → (¬ X ≃ ¬ Y)
equiv-neg {l1} {l2} {X} {Y} e =
  equiv-iff'
    ( neg-type-Prop X)
    ( neg-type-Prop Y)
    ( pair (map-neg (map-inv-equiv e)) (map-neg (map-equiv e)))
```

### Negation has no fixed points

```agda
no-fixed-points-neg :
  {l : Level} (A : UU l) → ¬ (A ↔ ¬ A)
no-fixed-points-neg A (f , g) =
  ( λ (h : ¬ A) → h (g h)) (λ (a : A) → f a a)

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
