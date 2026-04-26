# Functoriality of the type of linear combinations of elements of semirings

```agda
module ring-theory.functoriality-linear-combinations-of-elements-semirings where
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
open import foundation.images-subtypes
open import foundation.pullbacks-subtypes
open import foundation.singleton-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids

open import lists.functoriality-lists
open import lists.lists

open import ring-theory.homomorphisms-semirings
open import ring-theory.linear-combinations-of-elements-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings

open import structured-types.magmas
open import structured-types.morphisms-unital-magmas
```

</details>

## Idea

Consider a [semiring homomorphism](ring-theory.homomorphisms-semirings.md) `f : R → S` and a map `g : A → B`. A [linear combination of elements](ring-theory.linear-combinations-of-elements-semirings.md) `ℓ` in `A` with respect to the [semiring](ring-theory.semirings.md) `R` then gives a linear combination of elements `f ℓ` in `B` with respect to `S`.

## Definitions

### The induced map from linear combinations of elements in `R` to linear combinations of elements in `S`

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  map-linear-combination-Semiring :
    linear-combination-Semiring R A →
    linear-combination-Semiring S B
  map-linear-combination-Semiring =
    map-list
      ( map-product
        ( map-hom-Semiring R S f) (map-product g (map-hom-Semiring R S f)))
```

## Properties

### The functoriality of linear combinations preserves multiplying by a scalar from the left, from the right, and from both sides

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  preserves-left-mul-map-linear-combination-Semiring :
    (s : type-Semiring R) →
    (l : linear-combination-Semiring R A) →
    map-linear-combination-Semiring R S f g
      ( left-mul-linear-combination-Semiring R s l) ＝
    left-mul-linear-combination-Semiring S
      ( map-hom-Semiring R S f s)
      ( map-linear-combination-Semiring R S f g l)
  preserves-left-mul-map-linear-combination-Semiring s nil = refl
  preserves-left-mul-map-linear-combination-Semiring s (cons (r , a , u) l) =
    ap-cons
      ( eq-pair (preserves-mul-hom-Semiring R S f) refl)
      ( preserves-left-mul-map-linear-combination-Semiring s l)

  preserves-right-mul-map-linear-combination-Semiring :
    (l : linear-combination-Semiring R A) →
    (v : type-Semiring R) →
    map-linear-combination-Semiring R S f g
      ( right-mul-linear-combination-Semiring R l v) ＝
    right-mul-linear-combination-Semiring S
      ( map-linear-combination-Semiring R S f g l)
      ( map-hom-Semiring R S f v)
  preserves-right-mul-map-linear-combination-Semiring nil v = refl
  preserves-right-mul-map-linear-combination-Semiring (cons (r , a , u) l) v =
    ap-cons
      ( eq-pair refl (eq-pair refl (preserves-mul-hom-Semiring R S f)))
      ( preserves-right-mul-map-linear-combination-Semiring l v)

  preserves-mul-map-linear-combination-Semiring :
    (s : type-Semiring R) →
    (l : linear-combination-Semiring R A) →
    (v : type-Semiring R) →
    map-linear-combination-Semiring R S f g
      ( mul-linear-combination-Semiring R s l v) ＝
    mul-linear-combination-Semiring S
      ( map-hom-Semiring R S f s)
      ( map-linear-combination-Semiring R S f g l)
      ( map-hom-Semiring R S f v)
  preserves-mul-map-linear-combination-Semiring s nil v = refl
  preserves-mul-map-linear-combination-Semiring s (cons (r , a , u) l) v =
    ap-cons
      ( eq-pair
        ( preserves-mul-hom-Semiring R S f)
        ( eq-pair refl (preserves-mul-hom-Semiring R S f)))
      ( preserves-mul-map-linear-combination-Semiring s l v)
```

### The action on linear combinations of a semiring homomorphism preserves evaluation of linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
  (μ : type-Semiring R → A → type-Semiring R → type-Unital-Magma M)
  (ν : type-Semiring S → B → type-Semiring S → type-Unital-Magma N)
  (H :
    ( r : type-Semiring R) (a : A) (u : type-Semiring R) →
    map-hom-Unital-Magma M N h (μ r a u) ＝
    ν (map-hom-Semiring R S f r) (g a) (map-hom-Semiring R S f u))
  where

  preserves-ev-unital-magma-map-linear-combination-Semiring :
    (l : linear-combination-Semiring R A) →
    map-hom-Unital-Magma M N h
      ( ev-unital-magma-linear-combination-Semiring R M μ l) ＝
    ev-unital-magma-linear-combination-Semiring S N ν
      ( map-linear-combination-Semiring R S f g l)
  preserves-ev-unital-magma-map-linear-combination-Semiring nil =
    preserves-unit-hom-Unital-Magma M N h
  preserves-ev-unital-magma-map-linear-combination-Semiring
    ( cons (r , a , u) l) =
    preserves-mul-hom-Unital-Magma M N h ∙
    ap-binary
      ( mul-Unital-Magma N)
      ( H r a u)
      ( preserves-ev-unital-magma-map-linear-combination-Semiring l)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Monoid l5) (N : Monoid l6) (h : hom-Monoid M N)
  (μ : type-Semiring R → A → type-Semiring R → type-Monoid M)
  (ν : type-Semiring S → B → type-Semiring S → type-Monoid N)
  (H :
    ( r : type-Semiring R) (a : A) (u : type-Semiring R) →
    map-hom-Monoid M N h (μ r a u) ＝
    ν (map-hom-Semiring R S f r) (g a) (map-hom-Semiring R S f u))
  where

  preserves-ev-monoid-map-linear-combination-Semiring :
    (l : linear-combination-Semiring R A) →
    map-hom-Monoid M N h
      ( ev-monoid-linear-combination-Semiring R M μ l) ＝
    ev-monoid-linear-combination-Semiring S N ν
      ( map-linear-combination-Semiring R S f g l)
  preserves-ev-monoid-map-linear-combination-Semiring =
    preserves-ev-unital-magma-map-linear-combination-Semiring R S f g
      ( unital-magma-Monoid M)
      ( unital-magma-Monoid N)
      ( hom-unital-magma-hom-Monoid M N h)
      ( μ)
      ( ν)
      ( H)
```

### Functoriality of linear combinations preserve being linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  where

  module _
    (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
    (μ : type-Semiring R → A → type-Semiring R → type-Unital-Magma M)
    (ν : type-Semiring S → B → type-Semiring S → type-Unital-Magma N)
    (H :
      ( r : type-Semiring R) (a : A) (u : type-Semiring R) →
      map-hom-Unital-Magma M N h (μ r a u) ＝
      ν (map-hom-Semiring R S f r) (g a) (map-hom-Semiring R S f u))
    where

    map-is-linear-combination-Semiring :
      (x : type-Unital-Magma M) →
      is-linear-combination-Semiring R M μ x →
      is-linear-combination-Semiring S N ν (map-hom-Unital-Magma M N h x)
    map-is-linear-combination-Semiring _ (l , refl) =
      map-linear-combination-Semiring R S f g l ,
      inv
        ( preserves-ev-unital-magma-map-linear-combination-Semiring
          R S f g M N h μ ν H l)

  module _
    (M : Monoid l5) (N : Monoid l6) (h : hom-Monoid M N)
    (μ : type-Semiring R → A → type-Semiring R → type-Monoid M)
    (ν : type-Semiring S → B → type-Semiring S → type-Monoid N)
    (H :
      ( r : type-Semiring R) (a : A) (u : type-Semiring R) →
      map-hom-Monoid M N h (μ r a u) ＝
      ν (map-hom-Semiring R S f r) (g a) (map-hom-Semiring R S f u))
    where

    map-is-linear-combination-monoid-Semiring :
      (x : type-Monoid M) →
      is-linear-combination-monoid-Semiring R M μ x →
      is-linear-combination-monoid-Semiring S N ν (map-hom-Monoid M N h x)
    map-is-linear-combination-monoid-Semiring =
      map-is-linear-combination-Semiring
        ( unital-magma-Monoid M)
        ( unital-magma-Monoid N)
        ( hom-unital-magma-hom-Monoid M N h)
        ( μ)
        ( ν)
        ( H)
```

### Functoriality of linear combinations preserve being mere linear combinations

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {A : UU l3} {B : UU l4} (g : A → B)
  (M : Unital-Magma l5) (N : Unital-Magma l6) (h : hom-Unital-Magma M N)
  (μ : type-Semiring R → A → type-Semiring R → type-Unital-Magma M)
  (ν : type-Semiring S → B → type-Semiring S → type-Unital-Magma N)
  (H :
     ( r : type-Semiring R) (a : A) (u : type-Semiring R) →
     map-hom-Unital-Magma M N h (μ r a u) ＝
     ν (map-hom-Semiring R S f r) (g a) (map-hom-Semiring R S f u))
  where

  map-is-mere-linear-combination-Semiring :
    (x : type-Unital-Magma M) →
    is-mere-linear-combination-Semiring R M μ x →
    is-mere-linear-combination-Semiring S N ν (map-hom-Unital-Magma M N h x)
  map-is-mere-linear-combination-Semiring x =
    map-trunc-Prop (map-is-linear-combination-Semiring R S f g M N h μ ν H x)
```

### Functoriality of linear combinations of elements of subsets of a semiring

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  (U : subset-Semiring l3 R) (V : subset-Semiring l4 S)
  (g : U ⊆ pullback-subtype (map-hom-Semiring R S f) V)
  where

  map-linear-combination-subset-Semiring :
    linear-combination-subset-Semiring R U →
    linear-combination-subset-Semiring S V
  map-linear-combination-subset-Semiring =
    map-linear-combination-Semiring R S f
      ( map-type-subtype (map-hom-Semiring R S f) U V g)

  preserves-ev-map-linear-combination-subset-Semiring :
    (l : linear-combination-subset-Semiring R U) →
    map-hom-Semiring R S f
      ( ev-linear-combination-subset-Semiring R U l) ＝
    ev-linear-combination-subset-Semiring S V
      ( map-linear-combination-subset-Semiring l)
  preserves-ev-map-linear-combination-subset-Semiring =
    preserves-ev-unital-magma-map-linear-combination-Semiring R S f
      ( map-type-subtype (map-hom-Semiring R S f) U V g)
      ( additive-unital-magma-Semiring R)
      ( additive-unital-magma-Semiring S)
      ( hom-additive-unital-magma-hom-Semiring R S f)
      ( two-sided-scalar-multiplication-subset-Semiring R U)
      ( two-sided-scalar-multiplication-subset-Semiring S V)
      ( λ r (x , H) u →
        preserves-mul-hom-Semiring R S f ∙
        ap (mul-Semiring' S _) (preserves-mul-hom-Semiring R S f))

  map-is-linear-combination-subset-Semiring :
    (x : type-Semiring R) →
    is-linear-combination-subset-Semiring R U x →
    is-linear-combination-subset-Semiring S V (map-hom-Semiring R S f x)
  map-is-linear-combination-subset-Semiring =
    map-is-linear-combination-Semiring R S f
      ( map-type-subtype (map-hom-Semiring R S f) U V g)
      ( additive-unital-magma-Semiring R)
      ( additive-unital-magma-Semiring S)
      ( hom-additive-unital-magma-hom-Semiring R S f)
      ( two-sided-scalar-multiplication-subset-Semiring R U)
      ( two-sided-scalar-multiplication-subset-Semiring S V)
      ( λ r (x , H) u →
        preserves-mul-hom-Semiring R S f ∙
        ap (mul-Semiring' S _) (preserves-mul-hom-Semiring R S f))

  map-is-mere-linear-combination-subset-Semiring :
    (x : type-Semiring R) →
    is-mere-linear-combination-subset-Semiring R U x →
    is-mere-linear-combination-subset-Semiring S V (map-hom-Semiring R S f x)
  map-is-mere-linear-combination-subset-Semiring x =
    map-trunc-Prop (map-is-linear-combination-subset-Semiring x)
```

### Functoriality preserves linear combinations of families of elements in a semiring

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {I : UU l3} {J : UU l4}
  (a : I → type-Semiring R) (b : J → type-Semiring S)
  (g : subtype-im a ⊆ pullback-subtype (map-hom-Semiring R S f) (subtype-im b))
  where

  map-linear-combination-family-of-elements-Semiring :
    linear-combination-family-of-elements-Semiring R a →
    linear-combination-family-of-elements-Semiring S b
  map-linear-combination-family-of-elements-Semiring =
    map-linear-combination-subset-Semiring R S f (subtype-im a) (subtype-im b) g

  preserves-ev-map-linear-combination-family-of-elements-Semiring :
    (l : linear-combination-family-of-elements-Semiring R a) →
    map-hom-Semiring R S f
      ( ev-linear-combination-family-of-elements-Semiring R a l) ＝
    ev-linear-combination-family-of-elements-Semiring S b
      ( map-linear-combination-family-of-elements-Semiring l)
  preserves-ev-map-linear-combination-family-of-elements-Semiring =
    preserves-ev-map-linear-combination-subset-Semiring R S f
      ( subtype-im a)
      ( subtype-im b)
      ( g)

  map-is-linear-combination-family-of-elements-Semiring :
    (x : type-Semiring R) →
    is-linear-combination-family-of-elements-Semiring R a x →
    is-linear-combination-family-of-elements-Semiring S b
      ( map-hom-Semiring R S f x)
  map-is-linear-combination-family-of-elements-Semiring =
    map-is-linear-combination-subset-Semiring R S f
      ( subtype-im a)
      ( subtype-im b)
      ( g)
```

### Specific instance of functoriality preserving linear combinations of families of elements in a semiring

```agda
module _
  {l1 l2 l3 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  {I : UU l3} (a : I → type-Semiring R)
  where

  map-linear-combination-family-of-elements-Semiring' :
    linear-combination-family-of-elements-Semiring R a →
    linear-combination-family-of-elements-Semiring S
      ( map-hom-Semiring R S f ∘ a)
  map-linear-combination-family-of-elements-Semiring' =
    map-linear-combination-family-of-elements-Semiring R S f a
      ( map-hom-Semiring R S f ∘ a)
      ( inclusion-im-pullback-im-comp (map-hom-Semiring R S f) a)

  preserves-ev-map-linear-combination-family-of-elements-Semiring' :
    (l : linear-combination-family-of-elements-Semiring R a) →
    map-hom-Semiring R S f
      ( ev-linear-combination-family-of-elements-Semiring R a l) ＝
    ev-linear-combination-family-of-elements-Semiring S
      ( map-hom-Semiring R S f ∘ a)
      ( map-linear-combination-family-of-elements-Semiring' l)
  preserves-ev-map-linear-combination-family-of-elements-Semiring' =
    preserves-ev-map-linear-combination-family-of-elements-Semiring R S f a
      ( map-hom-Semiring R S f ∘ a)
      ( inclusion-im-pullback-im-comp (map-hom-Semiring R S f) a)

  map-is-linear-combination-family-of-elements-Semiring' :
    (x : type-Semiring R) →
    is-linear-combination-family-of-elements-Semiring R a x →
    is-linear-combination-family-of-elements-Semiring S
      ( map-hom-Semiring R S f ∘ a)
      ( map-hom-Semiring R S f x)
  map-is-linear-combination-family-of-elements-Semiring' =
    map-is-linear-combination-family-of-elements-Semiring R S f a
      ( map-hom-Semiring R S f ∘ a)
      ( inclusion-im-pullback-im-comp (map-hom-Semiring R S f) a)
```

map-linear-combination-family-of-elements-Semiring R S f x (map-hom-Semiring R S f ∘ x) (forward-implication-adjoint-relation-image-pullback-subtype (map-hom-Semiring R S f) (subtype-im x) (subtype-im (map-hom-Semiring R S f ∘ x)) {!!}) l , {!!}

### Functoriality preserves linear combinations of a single element in a semiring

```agda
module _
  {l1 l2 : Level}
  (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  (a : type-Semiring R)
  where

  map-linear-combination-element-Semiring :
    linear-combination-element-Semiring R a →
    linear-combination-element-Semiring S (map-hom-Semiring R S f a)
  map-linear-combination-element-Semiring =
    map-linear-combination-subset-Semiring R S f
      ( subtype-standard-singleton-subtype
        ( set-Semiring R)
        ( a))
      ( subtype-standard-singleton-subtype
        ( set-Semiring S)
        ( map-hom-Semiring R S f a))
      ( λ y → ap (map-hom-Semiring R S f))

  preserves-ev-map-linear-combination-element-Semiring :
    (l : linear-combination-element-Semiring R a) →
    map-hom-Semiring R S f (ev-linear-combination-element-Semiring R a l) ＝
    ev-linear-combination-element-Semiring S (map-hom-Semiring R S f a)
      ( map-linear-combination-element-Semiring l)
  preserves-ev-map-linear-combination-element-Semiring =
    preserves-ev-map-linear-combination-subset-Semiring R S f
      ( subtype-standard-singleton-subtype
        ( set-Semiring R)
        ( a))
      ( subtype-standard-singleton-subtype
        ( set-Semiring S)
        ( map-hom-Semiring R S f a))
      ( λ y → ap (map-hom-Semiring R S f))

  map-is-linear-combination-element-Semiring :
    (x : type-Semiring R) →
    is-linear-combination-element-Semiring R a x →
    is-linear-combination-element-Semiring S
      ( map-hom-Semiring R S f a)
      ( map-hom-Semiring R S f x)
  map-is-linear-combination-element-Semiring =
    map-is-linear-combination-subset-Semiring R S f
      ( subtype-standard-singleton-subtype
        ( set-Semiring R)
        ( a))
      ( subtype-standard-singleton-subtype
        ( set-Semiring S)
        ( map-hom-Semiring R S f a))
      ( λ y → ap (map-hom-Semiring R S f))
```
