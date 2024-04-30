# Unions of subtypes

```agda
module foundation.unions-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-locale-of-subtypes
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.least-upper-bounds-large-posets
```

</details>

## Idea

The **union** of two [subtypes](foundation-core.subtypes.md) `A` and `B` is the
subtype that contains the elements that are in `A` or in `B`.

## Definition

### Unions of subtypes

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  union-subtype : subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  union-subtype P Q x = (P x) ∨ (Q x)
  union-subtype P Q x = disjunction-Prop (P x) (Q x)

  infixl 10 _∪_
  _∪_ = union-subtype
```

### Unions of decidable subtypes

```agda
  union-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  union-decidable-subtype P Q x = disjunction-Decidable-Prop (P x) (Q x)
```

### Unions of families of subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  where

  union-family-of-subtypes :
    {I : UU l2} (A : I → subtype l3 X) → subtype (l2 ⊔ l3) X
  union-family-of-subtypes = sup-powerset-Large-Locale

  is-least-upper-bound-union-family-of-subtypes :
    {I : UU l2} (A : I → subtype l3 X) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( powerset-Large-Poset X)
      ( A)
      ( union-family-of-subtypes A)
  is-least-upper-bound-union-family-of-subtypes =
    is-least-upper-bound-sup-powerset-Large-Locale
```

## Properties

### The union of families of subtypes preserves indexed inclusion

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {I : UU l2}
  (A : I → subtype l3 X) (B : I → subtype l4 X)
  where

  preserves-order-union-family-of-subtypes :
    ((i : I) → A i ⊆ B i) →
    union-family-of-subtypes A ⊆ union-family-of-subtypes B
  preserves-order-union-family-of-subtypes H x p =
    apply-universal-property-trunc-Prop p
      ( union-family-of-subtypes B x)
      ( λ (i , q) → unit-trunc-Prop (i , H i x q))
```

## TODO: Change title

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) (Q : subtype l3 X)
  where

  subtype-union-left : P ⊆ union-subtype P Q
  subtype-union-left x = inl-disjunction-Prop (P x) (Q x)

  subtype-union-right : Q ⊆ union-subtype P Q
  subtype-union-right x = inr-disjunction-Prop (P x) (Q x)

  subtype-union-both :
    {l4 : Level} (S : subtype l4 X) → P ⊆ S → Q ⊆ S → union-subtype P Q ⊆ S
  subtype-union-both S P-sub-S Q-sub-S x =
    elim-disjunction-Prop (P x) (Q x) (S x) (P-sub-S x , Q-sub-S x)

module _
  {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) (Q : subtype l3 X)
  where

  subset-union-comm :
    union-subtype P Q ⊆ union-subtype Q P
  subset-union-comm =
    subtype-union-both P Q
      ( union-subtype Q P)
      ( subtype-union-right Q P)
      ( subtype-union-left Q P)

module _
  {l1 l2 l3 l4 : Level} {X : UU l1}
  (P : subtype l2 X) (Q : subtype l3 X) (S : subtype l4 X)
  where

  forward-subset-union-assoc :
    union-subtype P (union-subtype Q S) ⊆ union-subtype (union-subtype P Q) S
  forward-subset-union-assoc =
    subtype-union-both
      ( P)
      ( union-subtype Q S)
      ( union-subtype (union-subtype P Q) S)
      ( transitive-leq-subtype
        ( P)
        ( union-subtype P Q)
        ( union-subtype (union-subtype P Q) S)
        ( subtype-union-left (union-subtype P Q) S)
        ( subtype-union-left P Q))
      ( subtype-union-both Q S
        ( union-subtype (union-subtype P Q) S)
        ( transitive-leq-subtype
          ( Q)
          ( union-subtype P Q)
          ( union-subtype (union-subtype P Q) S)
          ( subtype-union-left (union-subtype P Q) S)
          ( subtype-union-right P Q))
        ( subtype-union-right (union-subtype P Q) S))

  backward-subset-union-assoc :
    union-subtype (union-subtype P Q) S ⊆ union-subtype P (union-subtype Q S)
  backward-subset-union-assoc =
    subtype-union-both
      ( union-subtype P Q)
      ( S)
      ( union-subtype P (union-subtype Q S))
      ( subtype-union-both P Q
        ( union-subtype P (union-subtype Q S))
        ( subtype-union-left P (union-subtype Q S))
        ( transitive-leq-subtype
          ( Q)
          ( union-subtype Q S)
          ( union-subtype P (union-subtype Q S))
          ( subtype-union-right P (union-subtype Q S))
          ( subtype-union-left Q S)))
      ( transitive-leq-subtype
        ( S)
        ( union-subtype Q S)
        ( union-subtype P (union-subtype Q S))
        ( subtype-union-right P (union-subtype Q S))
        ( subtype-union-right Q S))

module _
  {l1 : Level} {X : UU l1}
  where

  subset-union-subsets :
    {l2 l3 l4 l5 : Level}
    (P1 : subtype l2 X) (Q1 : subtype l3 X)
    (P2 : subtype l4 X) (Q2 : subtype l5 X) →
    P1 ⊆ P2 → Q1 ⊆ Q2 →
    union-subtype P1 Q1 ⊆ union-subtype P2 Q2
  subset-union-subsets P1 Q1 P2 Q2 P1-sub-P2 Q1-sub-Q2 =
    subtype-union-both P1 Q1 (union-subtype P2 Q2)
      ( transitive-leq-subtype P1 P2 (union-subtype P2 Q2)
        ( subtype-union-left P2 Q2)
        ( P1-sub-P2))
      ( transitive-leq-subtype Q1 Q2 (union-subtype P2 Q2)
        ( subtype-union-right P2 Q2)
        ( Q1-sub-Q2))

  subset-union-subset-left :
    {l2 l3 l4 : Level}
    (P1 : subtype l2 X) (P2 : subtype l3 X) (Q : subtype l4 X) →
    P1 ⊆ P2 →
    union-subtype P1 Q ⊆ union-subtype P2 Q
  subset-union-subset-left P1 P2 Q P1-sub-P2 =
    subtype-union-both P1 Q (union-subtype P2 Q)
      ( transitive-leq-subtype P1 P2 (union-subtype P2 Q)
        ( subtype-union-left P2 Q)
        ( P1-sub-P2))
      ( subtype-union-right P2 Q)

  subset-union-subset-right :
    {l2 l3 l4 : Level}
    (P : subtype l2 X) (Q1 : subtype l3 X) (Q2 : subtype l4 X) →
    Q1 ⊆ Q2 →
    union-subtype P Q1 ⊆ union-subtype P Q2
  subset-union-subset-right P Q1 Q2 Q1-sub-Q2 =
    subtype-union-both P Q1 (union-subtype P Q2)
      ( subtype-union-left P Q2)
      ( transitive-leq-subtype Q1 Q2 (union-subtype P Q2)
        ( subtype-union-right P Q2)
        ( Q1-sub-Q2))

module _
  {l1 l2 l3 l4 : Level} {X : UU l1}
  (P : subtype l2 X) (Q : subtype l3 X) (S : subtype l4 X)
  where

  union-swap-1-2 :
    union-subtype P (union-subtype Q S) ⊆ union-subtype Q (union-subtype P S)
  union-swap-1-2 =
    transitive-leq-subtype
      ( union-subtype P (union-subtype Q S))
      ( union-subtype (union-subtype Q P) S)
      ( union-subtype Q (union-subtype P S))
      ( backward-subset-union-assoc Q P S)
      ( transitive-leq-subtype
        ( union-subtype P (union-subtype Q S))
        ( union-subtype (union-subtype P Q) S)
        ( union-subtype (union-subtype Q P) S)
        ( subset-union-subset-left
          ( union-subtype P Q)
          ( union-subtype Q P)
          ( S)
          ( subset-union-comm P Q))
        ( forward-subset-union-assoc P Q S))

module _
  {l1 l2 : Level} {X : UU l1} (P : subtype l2 X)
  where

  subtype-union-same : union-subtype P P ⊆ P
  subtype-union-same =
    subtype-union-both P P P (refl-leq-subtype P) (refl-leq-subtype P)

  eq-union-same : P ＝ union-subtype P P
  eq-union-same =
    antisymmetric-leq-subtype
    ( P)
    ( union-subtype P P)
    ( subtype-union-left P P)
    ( subtype-union-same)
```
