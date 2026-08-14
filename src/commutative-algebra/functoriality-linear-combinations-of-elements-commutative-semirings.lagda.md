# Functoriality of the type of linear combinations of elements of commutative semirings

```agda
module
  commutative-algebra.functoriality-linear-combinations-of-elements-commutative-semirings
  where
```

<details><summary> Imports </summary>

```agda
open import commutative-algebra.homomorphisms-commutative-semirings
open import commutative-algebra.linear-combinations-of-elements-commutative-semirings
open import commutative-algebra.commutative-semirings
open import commutative-algebra.subsets-commutative-semirings

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.images
open import foundation.images-subtypes
open import foundation.pullbacks-subtypes
open import foundation.singleton-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids

open import lists.functoriality-lists
open import lists.lists

open import ring-theory.functoriality-linear-combinations-of-elements-semirings

open import structured-types.magmas
open import structured-types.morphisms-unital-magmas
```

</details>

## Idea

Consider a [commutative semiring homomorphism](commutative-algebra.homomorphisms-commutative-semirings.md) `f : R → S` and a map `g : A → B`. A [linear combination of elements](commutative-algebra.linear-combinations-of-elements-commutative-semirings.md) `ℓ` in `A` with respect to the [commutative-semiring](commutative-algebra.commutative-semirings.md) `R` then gives a linear combination of elements `f ℓ` in `B` with respect to `S`.

## Definitions

### The induced map from linear combinations of elements in `R` to linear combinations of elements in `S`

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  map-linear-combination-Commutative-Semiring :
    linear-combination-Commutative-Semiring R A →
    linear-combination-Commutative-Semiring S B
  map-linear-combination-Commutative-Semiring =
    map-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( g)
```

## Properties

### The functoriality of linear combinations preserves multiplying by a scalar from the left, from the right, and from both sides

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  preserves-left-mul-map-linear-combination-Commutative-Semiring :
    (s : type-Commutative-Semiring R) →
    (l : linear-combination-Commutative-Semiring R A) →
    map-linear-combination-Commutative-Semiring R S f g
      ( left-mul-linear-combination-Commutative-Semiring R s l) ＝
    left-mul-linear-combination-Commutative-Semiring S
      ( map-hom-Commutative-Semiring R S f s)
      ( map-linear-combination-Commutative-Semiring R S f g l)
  preserves-left-mul-map-linear-combination-Commutative-Semiring =
    preserves-left-mul-map-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( g)

  preserves-mul-map-linear-combination-Commutative-Semiring :
    (s : type-Commutative-Semiring R) →
    (l : linear-combination-Commutative-Semiring R A) →
    (v : type-Commutative-Semiring R) →
    map-linear-combination-Commutative-Semiring R S f g
      ( mul-linear-combination-Commutative-Semiring R s l v) ＝
    mul-linear-combination-Commutative-Semiring S
      ( map-hom-Commutative-Semiring R S f s)
      ( map-linear-combination-Commutative-Semiring R S f g l)
      ( map-hom-Commutative-Semiring R S f v)
  preserves-mul-map-linear-combination-Commutative-Semiring =
    preserves-mul-map-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( g)
```

### The action on linear combinations of a commutative semiring homomorphism preserves evaluation of linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
  (μ :
    type-Commutative-Semiring R → A →
    type-Commutative-Semiring R → type-Unital-Magma M)
  (ν :
    type-Commutative-Semiring S → B →
    type-Commutative-Semiring S → type-Unital-Magma N)
  (H :
    ( r : type-Commutative-Semiring R) (a : A)
    (u : type-Commutative-Semiring R) →
    map-hom-Unital-Magma M N h (μ r a u) ＝
    ν ( map-hom-Commutative-Semiring R S f r)
      ( g a)
      ( map-hom-Commutative-Semiring R S f u))
  where

  preserves-ev-unital-magma-map-linear-combination-Commutative-Semiring :
    (l : linear-combination-Commutative-Semiring R A) →
    map-hom-Unital-Magma M N h
      ( ev-unital-magma-linear-combination-Commutative-Semiring R M μ l) ＝
    ev-unital-magma-linear-combination-Commutative-Semiring S N ν
      ( map-linear-combination-Commutative-Semiring R S f g l)
  preserves-ev-unital-magma-map-linear-combination-Commutative-Semiring =
    preserves-ev-unital-magma-map-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( g)
      ( M)
      ( N)
      ( h)
      ( μ)
      ( ν)
      ( H)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Monoid l5) (N : Monoid l6) (h : hom-Monoid M N)
  (μ :
    type-Commutative-Semiring R → A →
    type-Commutative-Semiring R → type-Monoid M)
  (ν :
    type-Commutative-Semiring S → B →
    type-Commutative-Semiring S → type-Monoid N)
  (H :
    (r : type-Commutative-Semiring R) (a : A)
    (u : type-Commutative-Semiring R) →
    map-hom-Monoid M N h (μ r a u) ＝
    ν ( map-hom-Commutative-Semiring R S f r)
      ( g a)
      ( map-hom-Commutative-Semiring R S f u))
  where

  preserves-ev-monoid-map-linear-combination-Commutative-Semiring :
    (l : linear-combination-Commutative-Semiring R A) →
    map-hom-Monoid M N h
      ( ev-monoid-linear-combination-Commutative-Semiring R M μ l) ＝
    ev-monoid-linear-combination-Commutative-Semiring S N ν
      ( map-linear-combination-Commutative-Semiring R S f g l)
  preserves-ev-monoid-map-linear-combination-Commutative-Semiring =
    preserves-ev-monoid-map-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( g)
      ( M)
      ( N)
      ( h)
      ( μ)
      ( ν)
      ( H)
```

### Functoriality of linear combinations preserve being linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  module _
    (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
    (μ :
      type-Commutative-Semiring R → A →
      type-Commutative-Semiring R → type-Unital-Magma M)
    (ν :
      type-Commutative-Semiring S → B →
      type-Commutative-Semiring S → type-Unital-Magma N)
    (H :
      ( r : type-Commutative-Semiring R) (a : A)
      (u : type-Commutative-Semiring R) →
      map-hom-Unital-Magma M N h (μ r a u) ＝
      ν ( map-hom-Commutative-Semiring R S f r)
        ( g a)
        ( map-hom-Commutative-Semiring R S f u))
    where

    map-is-linear-combination-Commutative-Semiring :
      (x : type-Unital-Magma M) →
      is-linear-combination-Commutative-Semiring R M μ x →
      is-linear-combination-Commutative-Semiring S N ν
        ( map-hom-Unital-Magma M N h x)
    map-is-linear-combination-Commutative-Semiring =
      map-is-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( g)
      ( M)
      ( N)
      ( h)
      ( μ)
      ( ν)
      ( H)

  module _
    (M : Monoid l5) (N : Monoid l6) (h : hom-Monoid M N)
    (μ :
      type-Commutative-Semiring R → A →
      type-Commutative-Semiring R → type-Monoid M)
    (ν :
      type-Commutative-Semiring S → B →
      type-Commutative-Semiring S → type-Monoid N)
    (H :
      (r : type-Commutative-Semiring R) (a : A)
      (u : type-Commutative-Semiring R) →
      map-hom-Monoid M N h (μ r a u) ＝
      ν ( map-hom-Commutative-Semiring R S f r)
        ( g a)
        ( map-hom-Commutative-Semiring R S f u))
    where

    map-is-linear-combination-monoid-Commutative-Semiring :
      (x : type-Monoid M) →
      is-linear-combination-monoid-Commutative-Semiring R M μ x →
      is-linear-combination-monoid-Commutative-Semiring S N ν
        ( map-hom-Monoid M N h x)
    map-is-linear-combination-monoid-Commutative-Semiring =
      map-is-linear-combination-monoid-Semiring
        ( semiring-Commutative-Semiring R)
        ( semiring-Commutative-Semiring S)
        ( f)
        ( g)
        ( M)
        ( N)
        ( h)
        ( μ)
        ( ν)
        ( H)
```

### Functoriality of linear combinations preserve being mere linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
  (μ :
    type-Commutative-Semiring R → A →
    type-Commutative-Semiring R → type-Unital-Magma M)
  (ν :
    type-Commutative-Semiring S → B →
    type-Commutative-Semiring S → type-Unital-Magma N)
  (H :
    (r : type-Commutative-Semiring R) (a : A)
    (u : type-Commutative-Semiring R) →
    map-hom-Unital-Magma M N h (μ r a u) ＝
    ν ( map-hom-Commutative-Semiring R S f r)
      ( g a)
      ( map-hom-Commutative-Semiring R S f u))
  where

  map-is-mere-linear-combination-Commutative-Semiring :
    (x : type-Unital-Magma M) →
    is-mere-linear-combination-Commutative-Semiring R M μ x →
    is-mere-linear-combination-Commutative-Semiring S N ν
      ( map-hom-Unital-Magma M N h x)
  map-is-mere-linear-combination-Commutative-Semiring =
    map-is-mere-linear-combination-Semiring
        ( semiring-Commutative-Semiring R)
        ( semiring-Commutative-Semiring S)
        ( f)
        ( g)
        ( M)
        ( N)
        ( h)
        ( μ)
        ( ν)
        ( H)
```

### Functoriality of linear combinations of elements of subsets of a commutative semiring

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring R S)
  (U : subset-Commutative-Semiring l3 R) (V : subset-Commutative-Semiring l4 S)
  (g : U ⊆ pullback-subtype (map-hom-Commutative-Semiring R S f) V)
  where

  map-linear-combination-subset-Commutative-Semiring :
    linear-combination-subset-Commutative-Semiring R U →
    linear-combination-subset-Commutative-Semiring S V
  map-linear-combination-subset-Commutative-Semiring =
    map-linear-combination-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( U)
      ( V)
      ( g)

  preserves-ev-map-linear-combination-subset-Commutative-Semiring :
    (l : linear-combination-subset-Commutative-Semiring R U) →
    map-hom-Commutative-Semiring R S f
      ( ev-linear-combination-subset-Commutative-Semiring R U l) ＝
    ev-linear-combination-subset-Commutative-Semiring S V
      ( map-linear-combination-subset-Commutative-Semiring l)
  preserves-ev-map-linear-combination-subset-Commutative-Semiring =
    preserves-ev-map-linear-combination-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( U)
      ( V)
      ( g)

  map-is-linear-combination-subset-Commutative-Semiring :
    (x : type-Commutative-Semiring R) →
    is-linear-combination-subset-Commutative-Semiring R U x →
    is-linear-combination-subset-Commutative-Semiring S V
      ( map-hom-Commutative-Semiring R S f x)
  map-is-linear-combination-subset-Commutative-Semiring =
    map-is-linear-combination-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( U)
      ( V)
      ( g)

  map-is-mere-linear-combination-subset-Commutative-Semiring :
    (x : type-Commutative-Semiring R) →
    is-mere-linear-combination-subset-Commutative-Semiring R U x →
    is-mere-linear-combination-subset-Commutative-Semiring S V
      ( map-hom-Commutative-Semiring R S f x)
  map-is-mere-linear-combination-subset-Commutative-Semiring =
    map-is-mere-linear-combination-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( U)
      ( V)
      ( g)
```

### Functoriality preserves linear combinations of families of elements in a commutative semiring

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring R S)
  {I : UU l3} {J : UU l4}
  (a : I → type-Commutative-Semiring R) (b : J → type-Commutative-Semiring S)
  (g :
    subtype-im a ⊆
    pullback-subtype (map-hom-Commutative-Semiring R S f) (subtype-im b))
  where

  map-linear-combination-family-of-elements-Commutative-Semiring :
    linear-combination-family-of-elements-Commutative-Semiring R a →
    linear-combination-family-of-elements-Commutative-Semiring S b
  map-linear-combination-family-of-elements-Commutative-Semiring =
    map-linear-combination-family-of-elements-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( a)
      ( b)
      ( g)

  preserves-ev-map-linear-combination-family-of-elements-Commutative-Semiring :
    (l : linear-combination-family-of-elements-Commutative-Semiring R a) →
    map-hom-Commutative-Semiring R S f
      ( ev-linear-combination-family-of-elements-Commutative-Semiring R a l) ＝
    ev-linear-combination-family-of-elements-Commutative-Semiring S b
      ( map-linear-combination-family-of-elements-Commutative-Semiring l)
  preserves-ev-map-linear-combination-family-of-elements-Commutative-Semiring =
    preserves-ev-map-linear-combination-family-of-elements-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( a)
      ( b)
      ( g)

  map-is-linear-combination-family-of-elements-Commutative-Semiring :
    (x : type-Commutative-Semiring R) →
    is-linear-combination-family-of-elements-Commutative-Semiring R a x →
    is-linear-combination-family-of-elements-Commutative-Semiring S b
      ( map-hom-Commutative-Semiring R S f x)
  map-is-linear-combination-family-of-elements-Commutative-Semiring =
    map-is-linear-combination-family-of-elements-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( a)
      ( b)
      ( g)
```

### Specific instance of functoriality preserving linear combinations of families of elements in a commutative semiring

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring R S)
  {I : UU l3} (a : I → type-Commutative-Semiring R)
  where

  map-linear-combination-family-of-elements-Commutative-Semiring' :
    linear-combination-family-of-elements-Commutative-Semiring R a →
    linear-combination-family-of-elements-Commutative-Semiring S
      ( map-hom-Commutative-Semiring R S f ∘ a)
  map-linear-combination-family-of-elements-Commutative-Semiring' =
    map-linear-combination-family-of-elements-Semiring'
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( a)

  preserves-ev-map-linear-combination-family-of-elements-Commutative-Semiring' :
    (l : linear-combination-family-of-elements-Commutative-Semiring R a) →
    map-hom-Commutative-Semiring R S f
      ( ev-linear-combination-family-of-elements-Commutative-Semiring R a l) ＝
    ev-linear-combination-family-of-elements-Commutative-Semiring S
      ( map-hom-Commutative-Semiring R S f ∘ a)
      ( map-linear-combination-family-of-elements-Commutative-Semiring' l)
  preserves-ev-map-linear-combination-family-of-elements-Commutative-Semiring' =
    preserves-ev-map-linear-combination-family-of-elements-Semiring'
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( a)

  map-is-linear-combination-family-of-elements-Commutative-Semiring' :
    (x : type-Commutative-Semiring R) →
    is-linear-combination-family-of-elements-Commutative-Semiring R a x →
    is-linear-combination-family-of-elements-Commutative-Semiring S
      ( map-hom-Commutative-Semiring R S f ∘ a)
      ( map-hom-Commutative-Semiring R S f x)
  map-is-linear-combination-family-of-elements-Commutative-Semiring' =
    map-is-linear-combination-family-of-elements-Semiring'
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( a)
```

### Functoriality preserves linear combinations of a single element in a commutative semiring

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring R S)
  (a : type-Commutative-Semiring R)
  where

  map-linear-combination-element-Commutative-Semiring :
    linear-combination-element-Commutative-Semiring R a →
    linear-combination-element-Commutative-Semiring S
      ( map-hom-Commutative-Semiring R S f a)
  map-linear-combination-element-Commutative-Semiring =
    map-linear-combination-element-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( a)

  preserves-ev-map-linear-combination-element-Commutative-Semiring :
    (l : linear-combination-element-Commutative-Semiring R a) →
    map-hom-Commutative-Semiring R S f
      ( ev-linear-combination-element-Commutative-Semiring R a l) ＝
    ev-linear-combination-element-Commutative-Semiring S
      ( map-hom-Commutative-Semiring R S f a)
      ( map-linear-combination-element-Commutative-Semiring l)
  preserves-ev-map-linear-combination-element-Commutative-Semiring =
    preserves-ev-map-linear-combination-element-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( a)

  map-is-linear-combination-element-Commutative-Semiring :
    (x : type-Commutative-Semiring R) →
    is-linear-combination-element-Commutative-Semiring R a x →
    is-linear-combination-element-Commutative-Semiring S
      ( map-hom-Commutative-Semiring R S f a)
      ( map-hom-Commutative-Semiring R S f x)
  map-is-linear-combination-element-Commutative-Semiring =
    map-is-linear-combination-element-Semiring
      ( semiring-Commutative-Semiring R)
      ( semiring-Commutative-Semiring S)
      ( f)
      ( a)
```
