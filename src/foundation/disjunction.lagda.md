# Disjunction

```agda
module foundation.disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.functoriality-coproduct-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
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
{{#concept "disjunction" Disambiguation="of propositions" WDID=Q1651704 Agda=disjunction-Prop}}
of two [propositions](foundation-core.propositions.md) `P` and `Q` is the
proposition that `P` holds or `Q` holds, and is defined as
[propositional truncation](foundation.propositional-truncations.md) of the
[coproduct](foundation-core.coproduct-types.md) of their underlying types

```text
  P ∨ Q := ║ P + Q ║₋₁
```

The
{{#concept "universal property" Disambiguation="of the disjunction" Agda=universal-property-disjunction-Prop}}
of the disjunction states that, for every proposition `R`, the evaluation map

```text
  ev : ((P ∨ Q) → R) → ((P → R) ∧ (Q → R))
```

is a [logical equivalence](foundation.logical-equivalences.md), and thus the
disjunction is the least upper bound of `P` and `Q` in the
[poset of propositions](foundation.large-locale-of-propositions.md): there is a
pair of logical implications `P → R` and `Q → R`, if and only if `P ∨ Q` implies
`R`

```text
P ---> P ∨ Q <--- Q
  \      :      /
    \    :    /
      ∨  ∨  ∨
         R.
```

## Definitions

### The disjunction of arbitrary types

Given arbitrary types `A` and `B`, the truncation

```text
  ║ A + B ║₋₁
```

satisfies the universal property of

```text
  ║ A ║₋₁ ∨ ║ B ║₋₁
```

and is thus equivalent to it. Therefore, we may reasonably call this
construction the
{{#concept "disjunction" Disambiguation="of types" Agda=disjunction-prop-Type}}
of types. It is important to keep in mind that this is not a generalization of
the concept but rather a conflation, and should be read as the statement _`A` or
`B` is (merely) [inhabited](foundation.inhabited-types.md)_. Still, it is useful
to begin by considering disjunction on arbitrary types, as many constructions
pertaining to disjunction apply in this context, and it enables the inference
mechanism of Agda to do more work for us.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  disjunction-prop-Type : Prop (l1 ⊔ l2)
  disjunction-prop-Type = trunc-Prop (A + B)

  disjunction-Type : UU (l1 ⊔ l2)
  disjunction-Type = type-Prop disjunction-prop-Type

  is-prop-disjunction-Type : is-prop disjunction-Type
  is-prop-disjunction-Type = is-prop-type-Prop disjunction-prop-Type

  infixr 10 _∨_
  _∨_ : UU (l1 ⊔ l2)
  _∨_ = disjunction-Type
```

### The disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  disjunction-Prop : Prop (l1 ⊔ l2)
  disjunction-Prop = disjunction-prop-Type (type-Prop P) (type-Prop Q)

  type-disjunction-Prop : UU (l1 ⊔ l2)
  type-disjunction-Prop = type-Prop disjunction-Prop

  abstract
    is-prop-disjunction-Prop : is-prop type-disjunction-Prop
    is-prop-disjunction-Prop = is-prop-type-Prop disjunction-Prop

  infixr 10 _∨₍₋₁₎_
  _∨₍₋₁₎_ : Prop (l1 ⊔ l2)
  _∨₍₋₁₎_ = disjunction-Prop
```

The indexing $-1$ for the infix binary operator `∨₍₋₁₎` is part of a general
scheme, where `∨₍ₙ₎` takes as inputs
$n$-[types](foundation-core.truncated-types.md), and spits out the propositional
disjunction of their underlying types, as an $n$-type. This is in contrast to
the coproduct `+₍ₙ₎`, which will take values in $n$-types that are not generally
$k$-truncated for any $k < n$.

**Notation.** The symbol used for the disjunction `_∨₍₋₁₎_` is the
[logical or](https://codepoints.net/U+2228) `∨` (agda-input: `\vee` `\or`), and
not the [latin small letter v](https://codepoints.net/U+0076) `v`.

### The introduction rules for the disjunction

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  inl-disjunction : A → A ∨ B
  inl-disjunction = unit-trunc-Prop ∘ inl

  inr-disjunction : B → A ∨ B
  inr-disjunction = unit-trunc-Prop ∘ inr
```

### The universal property of disjunctions

```agda
ev-disjunction :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (A ∨ B → C) → (A → C) × (B → C)
pr1 (ev-disjunction h) = h ∘ inl-disjunction
pr2 (ev-disjunction h) = h ∘ inr-disjunction

universal-property-disjunction-Type :
  {l1 l2 l3 : Level} → UU l1 → UU l2 → Prop l3 → UUω
universal-property-disjunction-Type A B A∨B =
  {l : Level} (R : Prop l) →
  (type-Prop A∨B → type-Prop R) ↔ ((A → type-Prop R) × (B → type-Prop R))

universal-property-disjunction-Prop :
  {l1 l2 l3 : Level} → Prop l1 → Prop l2 → Prop l3 → UUω
universal-property-disjunction-Prop P Q =
  universal-property-disjunction-Type (type-Prop P) (type-Prop Q)
```

## Properties

### The disjunction satisfies the universal property of disjunctions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  elim-disjunction :
    {l : Level} (R : Prop l) →
    (A → type-Prop R) × (B → type-Prop R) → A ∨ B → type-Prop R
  elim-disjunction R (f , g) =
    map-universal-property-trunc-Prop R (rec-coproduct f g)

  up-disjunction :
    universal-property-disjunction-Type A B (disjunction-prop-Type A B)
  up-disjunction R = ev-disjunction , elim-disjunction R
```

### The recursion principle of disjunctions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (R : Prop l3)
  where

  rec-disjunction :
    (A → type-Prop R) → (B → type-Prop R) → A ∨ B → type-Prop R
  rec-disjunction f g = elim-disjunction R (f , g)
```

### Propositions that satisfy the universal property of a disjunction are equivalent to the disjunction

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (Q : Prop l3)
  (up-Q : universal-property-disjunction-Type A B Q)
  where

  forward-implication-iff-universal-property-disjunction :
     disjunction-Type A B → type-Prop Q
  forward-implication-iff-universal-property-disjunction =
    rec-disjunction Q
      ( pr1 (forward-implication (up-Q Q) id))
      ( pr2 (forward-implication (up-Q Q) id))

  backward-implication-iff-universal-property-disjunction :
    type-Prop Q → disjunction-Type A B
  backward-implication-iff-universal-property-disjunction =
    backward-implication
      ( up-Q (disjunction-prop-Type A B))
      ( inl-disjunction , inr-disjunction)

  iff-universal-property-disjunction :
    disjunction-Type A B ↔ type-Prop Q
  iff-universal-property-disjunction =
    ( forward-implication-iff-universal-property-disjunction ,
      backward-implication-iff-universal-property-disjunction)
```

### The unit laws for the disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  map-left-unit-law-disjunction-is-empty-Prop :
    is-empty (type-Prop P) → type-disjunction-Prop P Q → type-Prop Q
  map-left-unit-law-disjunction-is-empty-Prop f =
    rec-disjunction Q (ex-falso ∘ f) id

  map-right-unit-law-disjunction-is-empty-Prop :
    is-empty (type-Prop Q) → type-disjunction-Prop P Q → type-Prop P
  map-right-unit-law-disjunction-is-empty-Prop f =
    rec-disjunction P id (ex-falso ∘ f)
```

### The unit laws for the disjunction of types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-left-unit-law-disjunction-is-empty-Type :
    is-empty A → A ∨ B → is-inhabited B
  map-left-unit-law-disjunction-is-empty-Type f =
    rec-disjunction (is-inhabited-Prop B) (ex-falso ∘ f) unit-trunc-Prop

  map-right-unit-law-disjunction-is-empty-Type :
    is-empty B → A ∨ B → is-inhabited A
  map-right-unit-law-disjunction-is-empty-Type f =
    rec-disjunction (is-inhabited-Prop A) unit-trunc-Prop (ex-falso ∘ f)
```

### The disjunction of arbitrary types is the disjunction of inhabitedness proofs

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  universal-property-disjunction-trunc :
    universal-property-disjunction-Type A B
      ( disjunction-Prop (trunc-Prop A) (trunc-Prop B))
  universal-property-disjunction-trunc R =
    ( λ f →
      ( f ∘ inl-disjunction ∘ unit-trunc-Prop ,
        f ∘ inr-disjunction ∘ unit-trunc-Prop)) ,
    ( λ (f , g) →
      rec-trunc-Prop R
        ( rec-coproduct (rec-trunc-Prop R f) (rec-trunc-Prop R g)))

  iff-compute-disjunction-trunc :
    disjunction-Type A B ↔ type-disjunction-Prop (trunc-Prop A) (trunc-Prop B)
  iff-compute-disjunction-trunc =
    iff-universal-property-disjunction
      ( disjunction-Prop (trunc-Prop A) (trunc-Prop B))
      ( universal-property-disjunction-trunc)
```

### The disjunction preserves decidability

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-disjunction :
    is-decidable A → is-decidable B → is-decidable (A ∨ B)
  is-decidable-disjunction is-decidable-A is-decidable-B =
    is-decidable-trunc-Prop-is-merely-decidable
      ( A + B)
      ( unit-trunc-Prop (is-decidable-coproduct is-decidable-A is-decidable-B))

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

  disjunction-Decidable-Prop : Decidable-Prop (l1 ⊔ l2)
  disjunction-Decidable-Prop =
    ( type-disjunction-Decidable-Prop ,
      is-prop-disjunction-Decidable-Prop ,
      is-decidable-disjunction
        ( is-decidable-Decidable-Prop P)
        ( is-decidable-Decidable-Prop Q))
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
