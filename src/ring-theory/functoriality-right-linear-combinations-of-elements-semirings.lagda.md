# Functoriality of the type of right linear combinations of elements of semirings

```agda
module ring-theory.functoriality-right-linear-combinations-of-elements-semirings where
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
open import ring-theory.right-linear-combinations-of-elements-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings

open import structured-types.magmas
open import structured-types.morphisms-unital-magmas
```

</details>

## Idea

Consider a [semiring homomorphism](ring-theory.homomorphisms-semirings.md) `f : R → S` and a map `g : A → B`. A [right linear combination of elements](ring-theory.right-linear-combinations-of-elements-semirings.md) `ℓ` in `A` with respect to the [semiring](ring-theory.semirings.md) `R` then gives a right linear combination of elements `f ℓ` in `B` with respect to `S`.

## Definitions

### The induced map from right linear combinations of elements in `R` to right linear combinations of elements in `S`

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  map-right-linear-combination-Semiring :
    right-linear-combination-Semiring R A →
    right-linear-combination-Semiring S B
  map-right-linear-combination-Semiring =
    map-list (map-product g (map-hom-Semiring R S f))
```

## Properties

### The functoriality of right linear combinations preserves multiplying by a scalar from the right, from the right, and from both sides

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  preserves-mul-right-map-right-linear-combination-Semiring :
    (l : right-linear-combination-Semiring R A) →
    (s : type-Semiring R) →
    map-right-linear-combination-Semiring R S f g
      ( mul-right-linear-combination-Semiring R l s) ＝
    mul-right-linear-combination-Semiring S
      ( map-right-linear-combination-Semiring R S f g l)
      ( map-hom-Semiring R S f s)
  preserves-mul-right-map-right-linear-combination-Semiring nil s = refl
  preserves-mul-right-map-right-linear-combination-Semiring (cons (r , a) l) s =
    ap-cons
      ( eq-pair refl (preserves-mul-hom-Semiring R S f))
      ( preserves-mul-right-map-right-linear-combination-Semiring l s)
```

### The action on right linear combinations of a semiring homomorphism preserves evaluation of right linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
  (μ : A → type-Semiring R → type-Unital-Magma M)
  (ν : B → type-Semiring S → type-Unital-Magma N)
  (H :
    (a : A) (r : type-Semiring R) →
    map-hom-Unital-Magma M N h (μ a r) ＝ ν (g a) (map-hom-Semiring R S f r))
  where

  preserves-ev-unital-magma-map-right-linear-combination-Semiring :
    (l : right-linear-combination-Semiring R A) →
    map-hom-Unital-Magma M N h
      ( ev-unital-magma-right-linear-combination-Semiring R M μ l) ＝
    ev-unital-magma-right-linear-combination-Semiring S N ν
      ( map-right-linear-combination-Semiring R S f g l)
  preserves-ev-unital-magma-map-right-linear-combination-Semiring nil =
    preserves-unit-hom-Unital-Magma M N h
  preserves-ev-unital-magma-map-right-linear-combination-Semiring
    ( cons (r , a) l) =
    preserves-mul-hom-Unital-Magma M N h ∙
    ap-binary
      ( mul-Unital-Magma N)
      ( H r a)
      ( preserves-ev-unital-magma-map-right-linear-combination-Semiring l)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Monoid l5) (N : Monoid l6) (h : hom-Monoid M N)
  (μ : A → type-Semiring R → type-Monoid M)
  (ν : B → type-Semiring S → type-Monoid N)
  (H :
    (a : A) (r : type-Semiring R) →
    map-hom-Monoid M N h (μ a r) ＝ ν (g a) (map-hom-Semiring R S f r))
  where

  preserves-ev-monoid-map-right-linear-combination-Semiring :
    (l : right-linear-combination-Semiring R A) →
    map-hom-Monoid M N h
      ( ev-monoid-right-linear-combination-Semiring R M μ l) ＝
    ev-monoid-right-linear-combination-Semiring S N ν
      ( map-right-linear-combination-Semiring R S f g l)
  preserves-ev-monoid-map-right-linear-combination-Semiring =
    preserves-ev-unital-magma-map-right-linear-combination-Semiring R S f g
      ( unital-magma-Monoid M)
      ( unital-magma-Monoid N)
      ( hom-unital-magma-hom-Monoid M N h)
      ( μ)
      ( ν)
      ( H)
```

### Functoriality of right linear combinations preserve being right linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  module _
    (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
    (μ : A → type-Semiring R → type-Unital-Magma M)
    (ν : B → type-Semiring S → type-Unital-Magma N)
    (H :
      (a : A) (r : type-Semiring R) →
      map-hom-Unital-Magma M N h (μ a r) ＝ ν (g a) (map-hom-Semiring R S f r))
    where

    map-is-right-linear-combination-Semiring :
      (x : type-Unital-Magma M) →
      is-right-linear-combination-Semiring R M μ x →
      is-right-linear-combination-Semiring S N ν (map-hom-Unital-Magma M N h x)
    map-is-right-linear-combination-Semiring _ (l , refl) =
      map-right-linear-combination-Semiring R S f g l ,
      inv
        ( preserves-ev-unital-magma-map-right-linear-combination-Semiring
          R S f g M N h μ ν H l)

  module _
    (M : Monoid l5) (N : Monoid l6) (h : hom-Monoid M N)
    (μ : A → type-Semiring R → type-Monoid M)
    (ν : B → type-Semiring S → type-Monoid N)
    (H :
      (a : A) (r : type-Semiring R) →
      map-hom-Monoid M N h (μ a r) ＝ ν (g a) (map-hom-Semiring R S f r))
    where

    map-is-right-linear-combination-monoid-Semiring :
      (x : type-Monoid M) →
      is-right-linear-combination-monoid-Semiring R M μ x →
      is-right-linear-combination-monoid-Semiring S N ν (map-hom-Monoid M N h x)
    map-is-right-linear-combination-monoid-Semiring =
      map-is-right-linear-combination-Semiring
        ( unital-magma-Monoid M)
        ( unital-magma-Monoid N)
        ( hom-unital-magma-hom-Monoid M N h)
        ( μ)
        ( ν)
        ( H)
```

### Functoriality of right linear combinations preserve being mere right linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
  (μ : A → type-Semiring R → type-Unital-Magma M)
  (ν : B → type-Semiring S → type-Unital-Magma N)
  (H :
     (a : A) (r : type-Semiring R) →
     map-hom-Unital-Magma M N h (μ a r) ＝ ν (g a) (map-hom-Semiring R S f r))
  where

  map-is-mere-right-linear-combination-Semiring :
    (x : type-Unital-Magma M) →
    is-mere-right-linear-combination-Semiring R M μ x →
    is-mere-right-linear-combination-Semiring S N ν
      ( map-hom-Unital-Magma M N h x)
  map-is-mere-right-linear-combination-Semiring x =
    map-trunc-Prop
      ( map-is-right-linear-combination-Semiring R S f g M N h μ ν H x)
```

### Functoriality of right linear combinations of elements of subsets of a semiring

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  (U : subset-Semiring l3 R) (V : subset-Semiring l4 S)
  (g : U ⊆ pullback-subtype (map-hom-Semiring R S f) V)
  where

  map-right-linear-combination-subset-Semiring :
    right-linear-combination-subset-Semiring R U →
    right-linear-combination-subset-Semiring S V
  map-right-linear-combination-subset-Semiring =
    map-right-linear-combination-Semiring R S f
      ( map-type-subtype (map-hom-Semiring R S f) U V g)

  preserves-ev-map-right-linear-combination-subset-Semiring :
    (l : right-linear-combination-subset-Semiring R U) →
    map-hom-Semiring R S f
      ( ev-right-linear-combination-subset-Semiring R U l) ＝
    ev-right-linear-combination-subset-Semiring S V
      ( map-right-linear-combination-subset-Semiring l)
  preserves-ev-map-right-linear-combination-subset-Semiring =
    preserves-ev-unital-magma-map-right-linear-combination-Semiring R S f
      ( map-type-subtype (map-hom-Semiring R S f) U V g)
      ( additive-unital-magma-Semiring R)
      ( additive-unital-magma-Semiring S)
      ( hom-additive-unital-magma-hom-Semiring R S f)
      ( right-scalar-multiplication-subset-Semiring R U)
      ( right-scalar-multiplication-subset-Semiring S V)
      ( λ (x , H) r → preserves-mul-hom-Semiring R S f)

  map-is-right-linear-combination-subset-Semiring :
    (x : type-Semiring R) →
    is-right-linear-combination-subset-Semiring R U x →
    is-right-linear-combination-subset-Semiring S V (map-hom-Semiring R S f x)
  map-is-right-linear-combination-subset-Semiring =
    map-is-right-linear-combination-Semiring R S f
      ( map-type-subtype (map-hom-Semiring R S f) U V g)
      ( additive-unital-magma-Semiring R)
      ( additive-unital-magma-Semiring S)
      ( hom-additive-unital-magma-hom-Semiring R S f)
      ( right-scalar-multiplication-subset-Semiring R U)
      ( right-scalar-multiplication-subset-Semiring S V)
      ( λ (x , H) r → preserves-mul-hom-Semiring R S f)

  map-is-mere-right-linear-combination-subset-Semiring :
    (x : type-Semiring R) →
    is-mere-right-linear-combination-subset-Semiring R U x →
    is-mere-right-linear-combination-subset-Semiring S V
      ( map-hom-Semiring R S f x)
  map-is-mere-right-linear-combination-subset-Semiring x =
    map-trunc-Prop (map-is-right-linear-combination-subset-Semiring x)
```

### Functoriality preserves right linear combinations of families of elements in a semiring

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {I : UU l3} {J : UU l4}
  (a : I → type-Semiring R) (b : J → type-Semiring S)
  (g : subtype-im a ⊆ pullback-subtype (map-hom-Semiring R S f) (subtype-im b))
  where

  map-right-linear-combination-family-of-elements-Semiring :
    right-linear-combination-family-of-elements-Semiring R a →
    right-linear-combination-family-of-elements-Semiring S b
  map-right-linear-combination-family-of-elements-Semiring =
    map-right-linear-combination-subset-Semiring R S f
      ( subtype-im a)
      ( subtype-im b)
      ( g)

  preserves-ev-map-right-linear-combination-family-of-elements-Semiring :
    (l : right-linear-combination-family-of-elements-Semiring R a) →
    map-hom-Semiring R S f
      ( ev-right-linear-combination-family-of-elements-Semiring R a l) ＝
    ev-right-linear-combination-family-of-elements-Semiring S b
      ( map-right-linear-combination-family-of-elements-Semiring l)
  preserves-ev-map-right-linear-combination-family-of-elements-Semiring =
    preserves-ev-map-right-linear-combination-subset-Semiring R S f
      ( subtype-im a)
      ( subtype-im b)
      ( g)

  map-is-right-linear-combination-family-of-elements-Semiring :
    (x : type-Semiring R) →
    is-right-linear-combination-family-of-elements-Semiring R a x →
    is-right-linear-combination-family-of-elements-Semiring S b
      ( map-hom-Semiring R S f x)
  map-is-right-linear-combination-family-of-elements-Semiring =
    map-is-right-linear-combination-subset-Semiring R S f
      ( subtype-im a)
      ( subtype-im b)
      ( g)
```
