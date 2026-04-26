# Functoriality of the type of left linear combinations of elements of semirings

```agda
module ring-theory.functoriality-left-linear-combinations-of-elements-semirings where
```

<details><summary> Imports </summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.images
open import foundation.pullbacks-subtypes
open import foundation.singleton-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids

open import lists.functoriality-lists
open import lists.lists

open import ring-theory.homomorphisms-semirings
open import ring-theory.left-linear-combinations-of-elements-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings

open import structured-types.magmas
open import structured-types.morphisms-unital-magmas
```

</details>

## Idea

Consider a [semiring homomorphism](ring-theory.homomorphisms-semirings.md) `f : R → S` and a map `g : A → B`. A [left linear combination of elements](ring-theory.left-linear-combinations-of-elements-semirings.md) `ℓ` in `A` with respect to the [semiring](ring-theory.semirings.md) `R` then gives a left linear combination of elements `f ℓ` in `B` with respect to `S`.

## Definitions

### The induced map from left linear combinations of elements in `R` to left linear combinations of elements in `S`

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  map-left-linear-combination-Semiring :
    left-linear-combination-Semiring R A →
    left-linear-combination-Semiring S B
  map-left-linear-combination-Semiring =
    map-list (map-product (map-hom-Semiring R S f) g)
```

## Properties

### The functoriality of left linear combinations preserves multiplying by a scalar from the left, from the right, and from both sides

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  preserves-mul-left-map-left-linear-combination-Semiring :
    (s : type-Semiring R) →
    (l : left-linear-combination-Semiring R A) →
    map-left-linear-combination-Semiring R S f g
      ( mul-left-linear-combination-Semiring R s l) ＝
    mul-left-linear-combination-Semiring S
      ( map-hom-Semiring R S f s)
      ( map-left-linear-combination-Semiring R S f g l)
  preserves-mul-left-map-left-linear-combination-Semiring s nil = refl
  preserves-mul-left-map-left-linear-combination-Semiring s (cons (r , a) l) =
    ap-cons
      ( eq-pair (preserves-mul-hom-Semiring R S f) refl)
      ( preserves-mul-left-map-left-linear-combination-Semiring s l)
```

### The action on left linear combinations of a semiring homomorphism preserves evaluation of left linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
  (μ : type-Semiring R → A → type-Unital-Magma M)
  (ν : type-Semiring S → B → type-Unital-Magma N)
  (H :
    ( r : type-Semiring R) (a : A) →
    map-hom-Unital-Magma M N h (μ r a) ＝ ν (map-hom-Semiring R S f r) (g a))
  where

  preserves-ev-unital-magma-map-left-linear-combination-Semiring :
    (l : left-linear-combination-Semiring R A) →
    map-hom-Unital-Magma M N h
      ( ev-unital-magma-left-linear-combination-Semiring R M μ l) ＝
    ev-unital-magma-left-linear-combination-Semiring S N ν
      ( map-left-linear-combination-Semiring R S f g l)
  preserves-ev-unital-magma-map-left-linear-combination-Semiring nil =
    preserves-unit-hom-Unital-Magma M N h
  preserves-ev-unital-magma-map-left-linear-combination-Semiring
    ( cons (r , a) l) =
    preserves-mul-hom-Unital-Magma M N h ∙
    ap-binary
      ( mul-Unital-Magma N)
      ( H r a)
      ( preserves-ev-unital-magma-map-left-linear-combination-Semiring l)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Monoid l5) (N : Monoid l6) (h : hom-Monoid M N)
  (μ : type-Semiring R → A → type-Monoid M)
  (ν : type-Semiring S → B → type-Monoid N)
  (H :
    ( r : type-Semiring R) (a : A) →
    map-hom-Monoid M N h (μ r a) ＝ ν (map-hom-Semiring R S f r) (g a))
  where

  preserves-ev-monoid-map-left-linear-combination-Semiring :
    (l : left-linear-combination-Semiring R A) →
    map-hom-Monoid M N h
      ( ev-monoid-left-linear-combination-Semiring R M μ l) ＝
    ev-monoid-left-linear-combination-Semiring S N ν
      ( map-left-linear-combination-Semiring R S f g l)
  preserves-ev-monoid-map-left-linear-combination-Semiring =
    preserves-ev-unital-magma-map-left-linear-combination-Semiring R S f g
      ( unital-magma-Monoid M)
      ( unital-magma-Monoid N)
      ( hom-unital-magma-hom-Monoid M N h)
      ( μ)
      ( ν)
      ( H)
```

### Functoriality of left linear combinations preserve being left linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  module _
    (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
    (μ : type-Semiring R → A → type-Unital-Magma M)
    (ν : type-Semiring S → B → type-Unital-Magma N)
    (H :
      ( r : type-Semiring R) (a : A) →
      map-hom-Unital-Magma M N h (μ r a) ＝ ν (map-hom-Semiring R S f r) (g a))
    where

    map-is-left-linear-combination-Semiring :
      (x : type-Unital-Magma M) →
      is-left-linear-combination-Semiring R M μ x →
      is-left-linear-combination-Semiring S N ν (map-hom-Unital-Magma M N h x)
    map-is-left-linear-combination-Semiring _ (l , refl) =
      map-left-linear-combination-Semiring R S f g l ,
      inv
        ( preserves-ev-unital-magma-map-left-linear-combination-Semiring
          R S f g M N h μ ν H l)

  module _
    (M : Monoid l5) (N : Monoid l6) (h : hom-Monoid M N)
    (μ : type-Semiring R → A → type-Monoid M)
    (ν : type-Semiring S → B → type-Monoid N)
    (H :
      ( r : type-Semiring R) (a : A) →
      map-hom-Monoid M N h (μ r a) ＝
      ν (map-hom-Semiring R S f r) (g a))
    where

    map-is-left-linear-combination-monoid-Semiring :
      (x : type-Monoid M) →
      is-left-linear-combination-monoid-Semiring R M μ x →
      is-left-linear-combination-monoid-Semiring S N ν (map-hom-Monoid M N h x)
    map-is-left-linear-combination-monoid-Semiring =
      map-is-left-linear-combination-Semiring
        ( unital-magma-Monoid M)
        ( unital-magma-Monoid N)
        ( hom-unital-magma-hom-Monoid M N h)
        ( μ)
        ( ν)
        ( H)
```

### Functoriality of left linear combinations preserve being mere left linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
  (μ : type-Semiring R → A → type-Unital-Magma M)
  (ν : type-Semiring S → B → type-Unital-Magma N)
  (H :
     ( r : type-Semiring R) (a : A) →
     map-hom-Unital-Magma M N h (μ r a) ＝ ν (map-hom-Semiring R S f r) (g a))
  where

  map-is-mere-left-linear-combination-Semiring :
    (x : type-Unital-Magma M) →
    is-mere-left-linear-combination-Semiring R M μ x →
    is-mere-left-linear-combination-Semiring S N ν
      ( map-hom-Unital-Magma M N h x)
  map-is-mere-left-linear-combination-Semiring x =
    map-trunc-Prop
      ( map-is-left-linear-combination-Semiring R S f g M N h μ ν H x)
```

### Functoriality of left linear combinations of elements of subsets of a semiring

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  (U : subset-Semiring l3 R) (V : subset-Semiring l4 S)
  (g : U ⊆ pullback-subtype (map-hom-Semiring R S f) V)
  where

  map-left-linear-combination-subset-Semiring :
    left-linear-combination-subset-Semiring R U →
    left-linear-combination-subset-Semiring S V
  map-left-linear-combination-subset-Semiring =
    map-left-linear-combination-Semiring R S f
      ( map-type-subtype (map-hom-Semiring R S f) U V g)

  preserves-ev-map-left-linear-combination-subset-Semiring :
    (l : left-linear-combination-subset-Semiring R U) →
    map-hom-Semiring R S f
      ( ev-left-linear-combination-subset-Semiring R U l) ＝
    ev-left-linear-combination-subset-Semiring S V
      ( map-left-linear-combination-subset-Semiring l)
  preserves-ev-map-left-linear-combination-subset-Semiring =
    preserves-ev-unital-magma-map-left-linear-combination-Semiring R S f
      ( map-type-subtype (map-hom-Semiring R S f) U V g)
      ( additive-unital-magma-Semiring R)
      ( additive-unital-magma-Semiring S)
      ( hom-additive-unital-magma-hom-Semiring R S f)
      ( left-scalar-multiplication-subset-Semiring R U)
      ( left-scalar-multiplication-subset-Semiring S V)
      ( λ r (x , H) → preserves-mul-hom-Semiring R S f)

  map-is-left-linear-combination-subset-Semiring :
    (x : type-Semiring R) →
    is-left-linear-combination-subset-Semiring R U x →
    is-left-linear-combination-subset-Semiring S V (map-hom-Semiring R S f x)
  map-is-left-linear-combination-subset-Semiring =
    map-is-left-linear-combination-Semiring R S f
      ( map-type-subtype (map-hom-Semiring R S f) U V g)
      ( additive-unital-magma-Semiring R)
      ( additive-unital-magma-Semiring S)
      ( hom-additive-unital-magma-hom-Semiring R S f)
      ( left-scalar-multiplication-subset-Semiring R U)
      ( left-scalar-multiplication-subset-Semiring S V)
      ( λ r (x , H) → preserves-mul-hom-Semiring R S f)

  map-is-mere-left-linear-combination-subset-Semiring :
    (x : type-Semiring R) →
    is-mere-left-linear-combination-subset-Semiring R U x →
    is-mere-left-linear-combination-subset-Semiring S V
      ( map-hom-Semiring R S f x)
  map-is-mere-left-linear-combination-subset-Semiring x =
    map-trunc-Prop (map-is-left-linear-combination-subset-Semiring x)
```

### Functoriality preserves left linear combinations of families of elements in a semiring

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {I : UU l3} {J : UU l4}
  (a : I → type-Semiring R) (b : J → type-Semiring S)
  (g : subtype-im a ⊆ pullback-subtype (map-hom-Semiring R S f) (subtype-im b))
  where

  map-left-linear-combination-family-of-elements-Semiring :
    left-linear-combination-family-of-elements-Semiring R a →
    left-linear-combination-family-of-elements-Semiring S b
  map-left-linear-combination-family-of-elements-Semiring =
    map-left-linear-combination-subset-Semiring R S f
      ( subtype-im a)
      ( subtype-im b)
      ( g)

  preserves-ev-map-left-linear-combination-family-of-elements-Semiring :
    (l : left-linear-combination-family-of-elements-Semiring R a) →
    map-hom-Semiring R S f
      ( ev-left-linear-combination-family-of-elements-Semiring R a l) ＝
    ev-left-linear-combination-family-of-elements-Semiring S b
      ( map-left-linear-combination-family-of-elements-Semiring l)
  preserves-ev-map-left-linear-combination-family-of-elements-Semiring =
    preserves-ev-map-left-linear-combination-subset-Semiring R S f
      ( subtype-im a)
      ( subtype-im b)
      ( g)

  map-is-left-linear-combination-family-of-elements-Semiring :
    (x : type-Semiring R) →
    is-left-linear-combination-family-of-elements-Semiring R a x →
    is-left-linear-combination-family-of-elements-Semiring S b
      ( map-hom-Semiring R S f x)
  map-is-left-linear-combination-family-of-elements-Semiring =
    map-is-left-linear-combination-subset-Semiring R S f
      ( subtype-im a)
      ( subtype-im b)
      ( g)
```
