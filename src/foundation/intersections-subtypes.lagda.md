# Intersections of subtypes

```agda
module foundation.intersections-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.full-subtypes
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.large-locale-of-subtypes
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.propositions

open import group-theory.large-monoids
open import group-theory.large-semigroups

open import order-theory.greatest-lower-bounds-large-posets
```

</details>

## Idea

The
{{#concept "intersection" disambiguation="of two subtypes" WDID=Q185837 WD="intersection" Agda=intersection-subtype}}
of two [subtypes](foundation.subtypes.md) `A` and `B` is the subtype that
contains the elements that are in `A` [and](foundation.conjunction.md) in `B`.

Two subtypes
{{#concept "intersect" disambiguation="subtypes" Agda=intersect-subtype}} if
their intersection is [inhabited](foundation.inhabited-subtypes.md).

## Definition

### The intersection of two subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) (Q : subtype l3 X)
  where

  intersection-subtype : subtype (l2 ⊔ l3) X
  intersection-subtype = meet-powerset-Large-Locale P Q

  is-greatest-binary-lower-bound-intersection-subtype :
    is-greatest-binary-lower-bound-Large-Poset
      ( powerset-Large-Poset X)
      ( P)
      ( Q)
      ( intersection-subtype)
  pr1
    ( pr1
      ( is-greatest-binary-lower-bound-intersection-subtype R)
      ( p , q) x r) =
    p x r
  pr2
    ( pr1
      ( is-greatest-binary-lower-bound-intersection-subtype R)
      ( p , q) x r) = q x r
  pr1 (pr2 (is-greatest-binary-lower-bound-intersection-subtype R) p) x r =
    pr1 (p x r)
  pr2 (pr2 (is-greatest-binary-lower-bound-intersection-subtype R) p) x r =
    pr2 (p x r)
```

### The intersection of two decidable subtypes

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  intersection-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  intersection-decidable-subtype P Q x = conjunction-Decidable-Prop (P x) (Q x)
```

### The intersection of a family of subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  where

  intersection-family-of-subtypes :
    {I : UU l2} (P : I → subtype l3 X) → subtype (l2 ⊔ l3) X
  intersection-family-of-subtypes {I} P x = Π-Prop I (λ i → P i x)
```

### The proposition that two subtypes intersect

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) (Q : subtype l3 X)
  where

  intersect-prop-subtype : Prop (l1 ⊔ l2 ⊔ l3)
  intersect-prop-subtype = is-inhabited-subtype-Prop (intersection-subtype P Q)

  intersect-subtype : UU (l1 ⊔ l2 ⊔ l3)
  intersect-subtype = type-Prop intersect-prop-subtype
```

### The intersection operation is commutative

```agda
abstract
  commutative-intersection-subtype :
    {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) (Q : subtype l3 X) →
    intersection-subtype P Q ＝ intersection-subtype Q P
  commutative-intersection-subtype P Q =
    eq-has-same-elements-subtype _ _ (λ _ → iff-equiv commutative-product)
```

### The intersection operation is associative

```agda
abstract
  associative-intersection-subtype :
    {l1 l2 l3 l4 : Level} {X : UU l1} →
    (P : subtype l2 X) (Q : subtype l3 X) (R : subtype l4 X) →
    intersection-subtype (intersection-subtype P Q) R ＝
    intersection-subtype P (intersection-subtype Q R)
  associative-intersection-subtype P Q R =
    eq-has-same-elements-subtype _ _
      ( λ _ → iff-equiv (associative-product _ _ _))
```

### The intersection operation is idempotent

```agda
abstract
  idempotent-intersection-subtype :
    {l1 l2 : Level} {X : UU l1} (S : subtype l2 X) →
    intersection-subtype S S ＝ S
  idempotent-intersection-subtype S =
    eq-has-same-elements-subtype _ _ (λ x → (pr1 , λ x∈S → (x∈S , x∈S)))
```

### The full subtype is the identity for the intersection operation

```agda
abstract
  left-unit-law-intersection-subtype :
    {l1 l2 : Level} {X : UU l1} (P : subtype l2 X) →
    intersection-subtype (full-subtype lzero X) P ＝ P
  left-unit-law-intersection-subtype P =
    eq-has-same-elements-subtype _ _
      ( λ x → iff-equiv (left-unit-law-product-is-contr is-contr-raise-unit))

  right-unit-law-intersection-subtype :
    {l1 l2 : Level} {X : UU l1} (P : subtype l2 X) →
    intersection-subtype P (full-subtype lzero X) ＝ P
  right-unit-law-intersection-subtype P =
    commutative-intersection-subtype P _ ∙ left-unit-law-intersection-subtype P
```

### Intersection of subtypes preserves similarity

```agda
abstract
  preserves-sim-intersection-subtype :
    {l1 l2 l3 l4 l5 : Level} {X : UU l1} →
    (S : subtype l2 X) (T : subtype l3 X) → sim-subtype S T →
    (U : subtype l4 X) (V : subtype l5 X) → sim-subtype U V →
    sim-subtype (intersection-subtype S U) (intersection-subtype T V)
  preserves-sim-intersection-subtype _ _ (S⊆T , T⊆S) _ _ (U⊆V , V⊆U) =
    ( ( λ x → map-product (S⊆T x) (U⊆V x)) ,
      ( λ x → map-product (T⊆S x) (V⊆U x)))
```

### The large monoid of subtypes under intersection

```agda
module _
  {l : Level} (X : UU l)
  where

  large-semigroup-intersection-subtype : Large-Semigroup (λ l2 → l ⊔ lsuc l2)
  large-semigroup-intersection-subtype =
    make-Large-Semigroup
      ( powerset-Set X)
      ( intersection-subtype)
      ( associative-intersection-subtype)

  large-monoid-intersection-subtype :
    Large-Monoid (λ l2 → l ⊔ lsuc l2) (λ l1 l2 → l ⊔ l1 ⊔ l2)
  large-monoid-intersection-subtype =
    make-Large-Monoid
      ( large-semigroup-intersection-subtype)
      ( large-similarity-relation-sim-subtype X)
      ( λ l → raise-subtype l)
      ( sim-raise-subtype)
      ( preserves-sim-intersection-subtype)
      ( full-subtype lzero X)
      ( left-unit-law-intersection-subtype)
      ( right-unit-law-intersection-subtype)
```
