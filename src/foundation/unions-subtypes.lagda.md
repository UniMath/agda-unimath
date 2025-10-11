# Unions of subtypes

```agda
module foundation.unions-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-subtypes
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.large-locale-of-subtypes
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.large-monoids
open import group-theory.large-semigroups

open import logic.de-morgan-propositions
open import logic.de-morgan-subtypes
open import logic.double-negation-stable-subtypes

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
```

### Unions of decidable subtypes

```agda
  union-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  union-decidable-subtype P Q x = disjunction-Decidable-Prop (P x) (Q x)
```

### Unions of De Morgan subtypes

```agda
  union-de-morgan-subtype :
    de-morgan-subtype l1 X → de-morgan-subtype l2 X →
    de-morgan-subtype (l1 ⊔ l2) X
  union-de-morgan-subtype P Q x = disjunction-De-Morgan-Prop (P x) (Q x)
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

### The union operation is associative

```agda
abstract
  associative-union-subtype :
    {l1 l2 l3 l4 : Level} {X : UU l1}
    (S : subtype l2 X) (T : subtype l3 X) (U : subtype l4 X) →
    union-subtype (union-subtype S T) U ＝ union-subtype S (union-subtype T U)
  associative-union-subtype S T U =
    eq-has-same-elements-subtype _ _
      ( λ x → (right-associate-disjunction , left-associate-disjunction))
```

### The union operation is commutative

```agda
abstract
  commutative-union-subtype :
    {l1 l2 l3 : Level} {X : UU l1} (S : subtype l2 X) (T : subtype l3 X) →
    union-subtype S T ＝ union-subtype T S
  commutative-union-subtype S T =
    eq-has-same-elements-subtype _ _
      ( λ s → (swap-disjunction , swap-disjunction))
```

### The union operation is idempotent

```agda
abstract
  idempotent-union-subtype :
    {l1 l2 : Level} {X : UU l1} (S : subtype l2 X) → union-subtype S S ＝ S
  idempotent-union-subtype S =
    eq-has-same-elements-subtype _ _
      ( λ x → (elim-disjunction (S x) id id , inl-disjunction))
```

### The empty subtype is an identity for the union operation

```agda
abstract
  left-unit-law-union-subtype :
    {l1 l2 : Level} {X : UU l1} (S : subtype l2 X) →
    union-subtype (empty-subtype lzero X) S ＝ S
  left-unit-law-union-subtype {X = X} S =
    eq-has-same-elements-subtype _ _
      ( λ s →
        ( map-left-unit-law-disjunction-is-empty-Prop
            ( empty-subtype _ X s)
            ( S s)
            ( is-empty-subtype-empty-subtype X s) ,
          inr-disjunction))

  right-unit-law-union-subtype :
    {l1 l2 : Level} {X : UU l1} (S : subtype l2 X) →
    union-subtype S (empty-subtype lzero X) ＝ S
  right-unit-law-union-subtype S =
    ( commutative-union-subtype S (empty-subtype lzero _)) ∙
    ( left-unit-law-union-subtype S)
```

### The union operation preserves similarity of subtypes

```agda
abstract
  preserves-sim-union-subtype :
    {l1 l2 l3 l4 l5 : Level} {X : UU l1} →
    (S : subtype l2 X) (T : subtype l3 X) → sim-subtype S T →
    (U : subtype l4 X) (V : subtype l5 X) → sim-subtype U V →
    sim-subtype (union-subtype S U) (union-subtype T V)
  preserves-sim-union-subtype _ _ (S⊆T , T⊆S) _ _ (U⊆V , V⊆U) =
    ( ( λ x → map-disjunction (S⊆T x) (U⊆V x)) ,
      ( λ x → map-disjunction (T⊆S x) (V⊆U x)))
```

### The large monoid of subtypes under unions

```agda
module _
  {l : Level} (X : UU l)
  where

  large-semigroup-union-subtype : Large-Semigroup (λ l2 → l ⊔ lsuc l2)
  large-semigroup-union-subtype =
    make-Large-Semigroup
      ( powerset-Set X)
      ( union-subtype)
      ( associative-union-subtype)

  large-monoid-union-subtype :
    Large-Monoid (λ l2 → l ⊔ lsuc l2) (λ l1 l2 → l ⊔ l1 ⊔ l2)
  large-monoid-union-subtype =
    make-Large-Monoid
      ( large-semigroup-union-subtype)
      ( large-similarity-relation-sim-subtype X)
      ( λ l2 → raise-subtype l2)
      ( sim-raise-subtype)
      ( preserves-sim-union-subtype)
      ( empty-subtype lzero X)
      ( left-unit-law-union-subtype)
      ( right-unit-law-union-subtype)
```
