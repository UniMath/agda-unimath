# Disjunction

```agda
module foundation.disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.type-arithmetic-coproduct-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.negation
open import foundation-core.propositions

open import logic.propositionally-decidable-types
```

</details>

## Idea

The
{{#concept "disjunction" Disambiguation="of propositions" WDID=Q1651704 WD="logical disjunction" Agda=disjunction-Prop}}
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
[locale of propositions](foundation.large-locale-of-propositions.md): there is a
pair of logical implications `P → R` and `Q → R`, if and only if `P ∨ Q` implies
`R`

```text
P ---> P ∨ Q <--- Q
  \      ∶      /
    \    ∶    /
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
{{#concept "disjunction" Disambiguation="of types" Agda=disjunction-type-Prop}}
of types. It is important to keep in mind that this is not a generalization of
the concept but rather a conflation, and should be read as the statement _`A` or
`B` is (merely) [inhabited](foundation.inhabited-types.md)_.

Because propositions are a special case of types, and Agda can generally infer
types for us, we will continue to conflate the two in our formalizations for the
benefit that we have to specify the propositions in our code less often. For
instance, even though the introduction rules for disjunction are phrased in
terms of disjunction of types, they equally apply to disjunction of
propositions.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  disjunction-type-Prop : Prop (l1 ⊔ l2)
  disjunction-type-Prop = trunc-Prop (A + B)

  disjunction-type : UU (l1 ⊔ l2)
  disjunction-type = type-Prop disjunction-type-Prop

  is-prop-disjunction-type : is-prop disjunction-type
  is-prop-disjunction-type = is-prop-type-Prop disjunction-type-Prop
```

### The disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  disjunction-Prop : Prop (l1 ⊔ l2)
  disjunction-Prop = disjunction-type-Prop (type-Prop P) (type-Prop Q)

  type-disjunction-Prop : UU (l1 ⊔ l2)
  type-disjunction-Prop = type-Prop disjunction-Prop

  abstract
    is-prop-disjunction-Prop : is-prop type-disjunction-Prop
    is-prop-disjunction-Prop = is-prop-type-Prop disjunction-Prop

  infixr 10 _∨_
  _∨_ : Prop (l1 ⊔ l2)
  _∨_ = disjunction-Prop
```

**Notation.** The symbol used for the disjunction `_∨_` is the
[logical or](https://codepoints.net/U+2228) `∨` (agda-input: `\vee` `\or`), and
not the [latin small letter v](https://codepoints.net/U+0076) `v`.

### The introduction rules for the disjunction

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  inl-disjunction : A → disjunction-type A B
  inl-disjunction = unit-trunc-Prop ∘ inl

  inr-disjunction : B → disjunction-type A B
  inr-disjunction = unit-trunc-Prop ∘ inr
```

**Note.** Even though the introduction rules are formalized in terms of
disjunction of types, it equally applies to disjunction of propositions. This is
because propositions are a special case of types. The benefit of this approach
is that Agda can infer types for us, but not generally propositions.

### The universal property of disjunctions

```agda
ev-disjunction :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (disjunction-type A B → C) → (A → C) × (B → C)
pr1 (ev-disjunction h) = h ∘ inl-disjunction
pr2 (ev-disjunction h) = h ∘ inr-disjunction

universal-property-disjunction-type :
  {l1 l2 l3 : Level} → UU l1 → UU l2 → Prop l3 → UUω
universal-property-disjunction-type A B S =
  {l : Level} (R : Prop l) →
  (type-Prop S → type-Prop R) ↔ ((A → type-Prop R) × (B → type-Prop R))

universal-property-disjunction-Prop :
  {l1 l2 l3 : Level} → Prop l1 → Prop l2 → Prop l3 → UUω
universal-property-disjunction-Prop P Q =
  universal-property-disjunction-type (type-Prop P) (type-Prop Q)
```

## Properties

### The disjunction satisfies the universal property of disjunctions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  elim-disjunction' :
    {l : Level} (R : Prop l) →
    (A → type-Prop R) × (B → type-Prop R) →
    disjunction-type A B → type-Prop R
  elim-disjunction' R (f , g) =
    map-universal-property-trunc-Prop R (rec-coproduct f g)

  up-disjunction :
    universal-property-disjunction-type A B (disjunction-type-Prop A B)
  up-disjunction R = ev-disjunction , elim-disjunction' R
```

### The elimination principle of disjunctions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (R : Prop l3)
  where

  elim-disjunction :
    (A → type-Prop R) → (B → type-Prop R) →
    disjunction-type A B → type-Prop R
  elim-disjunction f g = elim-disjunction' R (f , g)
```

### Propositions that satisfy the universal property of a disjunction are equivalent to the disjunction

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (Q : Prop l3)
  (up-Q : universal-property-disjunction-type A B Q)
  where

  forward-implication-iff-universal-property-disjunction :
    disjunction-type A B → type-Prop Q
  forward-implication-iff-universal-property-disjunction =
    elim-disjunction Q
      ( pr1 (forward-implication (up-Q Q) id))
      ( pr2 (forward-implication (up-Q Q) id))

  backward-implication-iff-universal-property-disjunction :
    type-Prop Q → disjunction-type A B
  backward-implication-iff-universal-property-disjunction =
    backward-implication
      ( up-Q (disjunction-type-Prop A B))
      ( inl-disjunction , inr-disjunction)

  iff-universal-property-disjunction :
    disjunction-type A B ↔ type-Prop Q
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
    elim-disjunction Q (ex-falso ∘ f) id

  map-right-unit-law-disjunction-is-empty-Prop :
    is-empty (type-Prop Q) → type-disjunction-Prop P Q → type-Prop P
  map-right-unit-law-disjunction-is-empty-Prop f =
    elim-disjunction P id (ex-falso ∘ f)
```

### The unit laws for the disjunction of types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-left-unit-law-disjunction-is-empty-type :
    is-empty A → disjunction-type A B → is-inhabited B
  map-left-unit-law-disjunction-is-empty-type f =
    elim-disjunction (is-inhabited-Prop B) (ex-falso ∘ f) unit-trunc-Prop

  map-right-unit-law-disjunction-is-empty-type :
    is-empty B → disjunction-type A B → is-inhabited A
  map-right-unit-law-disjunction-is-empty-type f =
    elim-disjunction (is-inhabited-Prop A) unit-trunc-Prop (ex-falso ∘ f)
```

### The disjunction of arbitrary types is the disjunction of inhabitedness propositions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  universal-property-disjunction-trunc :
    universal-property-disjunction-type A B
      ( disjunction-Prop (trunc-Prop A) (trunc-Prop B))
  universal-property-disjunction-trunc R =
    ( λ f →
      ( f ∘ inl-disjunction ∘ unit-trunc-Prop ,
        f ∘ inr-disjunction ∘ unit-trunc-Prop)) ,
    ( λ (f , g) →
      rec-trunc-Prop R
        ( rec-coproduct (rec-trunc-Prop R f) (rec-trunc-Prop R g)))

  iff-compute-disjunction-trunc :
    disjunction-type A B ↔ type-disjunction-Prop (trunc-Prop A) (trunc-Prop B)
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
    is-decidable A → is-decidable B → is-decidable (disjunction-type A B)
  is-decidable-disjunction is-decidable-A is-decidable-B =
    is-decidable-trunc-Prop-is-merely-decidable
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

### Symmetry of the disjuction

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  swap-disjunction : disjunction-type A B → disjunction-type B A
  swap-disjunction = map-trunc-Prop map-commutative-coproduct
```

### Associativity of the disjunction

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  left-associate-disjunction :
    disjunction-type A (disjunction-type B C) →
    disjunction-type (disjunction-type A B) C
  left-associate-disjunction =
    elim-disjunction
      ( disjunction-type-Prop (disjunction-type A B) C)
      ( inl-disjunction ∘ inl-disjunction)
      ( map-trunc-Prop (map-coproduct inr-disjunction id))

  right-associate-disjunction :
    disjunction-type (disjunction-type A B) C →
    disjunction-type A (disjunction-type B C)
  right-associate-disjunction =
    elim-disjunction
      ( disjunction-type-Prop A (disjunction-type B C))
      ( map-trunc-Prop (map-coproduct id inl-disjunction))
      ( inr-disjunction ∘ inr-disjunction)

  associative-disjunction :
    disjunction-type (disjunction-type A B) C ↔
    disjunction-type A (disjunction-type B C)
  associative-disjunction =
    ( right-associate-disjunction , left-associate-disjunction)
```

### The disjunction of mutually exclusive types

If two propositions are mutually exclusive, then their disjunction is equivalent
to the coproduct of their underlying types

```text
  P ∨ Q = P + Q.
```

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  (f : type-Prop P → ¬ (type-Prop Q))
  where

  map-compute-disjunction-mutually-exclusive :
    type-disjunction-Prop P Q → type-Prop P + type-Prop Q
  map-compute-disjunction-mutually-exclusive =
    elim-disjunction (coproduct-Prop P Q f) inl inr

  compute-disjunction-mutually-exclusive :
    type-disjunction-Prop P Q ↔ type-Prop P + type-Prop Q
  compute-disjunction-mutually-exclusive =
    ( map-compute-disjunction-mutually-exclusive , unit-trunc-Prop)

  inv-compute-disjunction-mutually-exclusive :
    type-Prop P + type-Prop Q ↔ type-disjunction-Prop P Q
  inv-compute-disjunction-mutually-exclusive =
    inv-iff compute-disjunction-mutually-exclusive

  equiv-compute-disjunction-mutually-exclusive :
    type-disjunction-Prop P Q ≃ type-Prop P + type-Prop Q
  equiv-compute-disjunction-mutually-exclusive =
    equiv-iff'
      ( disjunction-Prop P Q)
      ( coproduct-Prop P Q f)
      ( compute-disjunction-mutually-exclusive)

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  (f : ║ A ║₋₁ → ¬ ║ B ║₋₁)
  where

  map-compute-disjunction-type-mutually-exclusive :
    disjunction-type A B → ║ A ║₋₁ + ║ B ║₋₁
  map-compute-disjunction-type-mutually-exclusive =
    elim-disjunction
      ( coproduct-Prop (trunc-Prop A) (trunc-Prop B) f)
      ( inl ∘ unit-trunc-Prop)
      ( inr ∘ unit-trunc-Prop)

  map-inv-compute-disjunction-type-mutually-exclusive :
    ║ A ║₋₁ + ║ B ║₋₁ → disjunction-type A B
  map-inv-compute-disjunction-type-mutually-exclusive (inl a) =
    rec-trunc-Prop (disjunction-type-Prop A B) inl-disjunction a
  map-inv-compute-disjunction-type-mutually-exclusive (inr b) =
    rec-trunc-Prop (disjunction-type-Prop A B) inr-disjunction b

  compute-disjunction-type-mutually-exclusive :
    disjunction-type A B ↔ (║ A ║₋₁ + ║ B ║₋₁)
  compute-disjunction-type-mutually-exclusive =
    ( map-compute-disjunction-type-mutually-exclusive ,
      map-inv-compute-disjunction-type-mutually-exclusive)

  inv-compute-disjunction-type-mutually-exclusive :
    (║ A ║₋₁ + ║ B ║₋₁) ↔ disjunction-type A B
  inv-compute-disjunction-type-mutually-exclusive =
    inv-iff compute-disjunction-type-mutually-exclusive

  equiv-compute-disjunction-type-mutually-exclusive :
    disjunction-type A B ≃ (║ A ║₋₁ + ║ B ║₋₁)
  equiv-compute-disjunction-type-mutually-exclusive =
    equiv-iff'
      ( disjunction-type-Prop A B)
      ( coproduct-Prop (trunc-Prop A) (trunc-Prop B) f)
      ( compute-disjunction-type-mutually-exclusive)
```

## See also

- The indexed counterpart to disjunction is
  [existential quantification](foundation.existential-quantification.md).

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [disjunction](https://ncatlab.org/nlab/show/disjunction) at $n$Lab
- [Logical disjunction](https://en.wikipedia.org/wiki/Logical_disjunction) at
  Wikipedia
