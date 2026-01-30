# Complemented subtypes

```agda
module measure-theory.complemented-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import measure-theory.apart-subtypes
```

</details>

## Idea

A
{{#concept "complemented subtype" Disambiguation="of a type with apartness" Agda=complemented-subtype-Type-With-Apartness}}
of a type `X` equipped with an
[apartness relation](foundation.apartness-relations.md) is an ordered pair of
[subtypes](foundation-core.subtypes.md) `A` and `A'` of `X` that are
[apart](measure-theory.apart-subtypes.md).

This definition follows {{#cite Zeuner22}}..

## Definition

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  complemented-subtype-Type-With-Apartness : (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  complemented-subtype-Type-With-Apartness l =
    Σ ( subtype l (type-Type-With-Apartness X))
      ( λ A →
        Σ ( subtype l (type-Type-With-Apartness X))
          ( apart-subtype-Type-With-Apartness X A))

module _
  {l1 l2 l : Level}
  (X : Type-With-Apartness l1 l2)
  (cA@(A , A' , A#A') : complemented-subtype-Type-With-Apartness X l)
  where

  subtype-complemented-subtype-Type-With-Apartness :
    subtype l (type-Type-With-Apartness X)
  subtype-complemented-subtype-Type-With-Apartness = A

  complement-subtype-complemented-subtype-Type-With-Apartness :
    subtype l (type-Type-With-Apartness X)
  complement-subtype-complemented-subtype-Type-With-Apartness = A'

  apart-subtype-complemented-subtype-Type-With-Apartness :
    apart-subtype-Type-With-Apartness
      ( X)
      ( subtype-complemented-subtype-Type-With-Apartness)
      ( complement-subtype-complemented-subtype-Type-With-Apartness)
  apart-subtype-complemented-subtype-Type-With-Apartness = A#A'
```

## Properties

### The complement of a complemented subtype

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Apartness l1 l2)
  where

  complement-complemented-subtype-Type-With-Apartness :
    {l : Level} → complemented-subtype-Type-With-Apartness X l →
    complemented-subtype-Type-With-Apartness X l
  complement-complemented-subtype-Type-With-Apartness (A , A' , A#A') =
    ( A' ,
      A ,
      λ a' a a'∈A' a∈A →
        symmetric-apart-Type-With-Apartness X a a' (A#A' a a' a∈A a'∈A'))
```

### The subtype and complement subtype associated with a complemented subtype are disjoint

```agda
module _
  {l1 l2 l : Level}
  (X : Type-With-Apartness l1 l2)
  (cA@(A , A' , A#A') : complemented-subtype-Type-With-Apartness X l)
  where

  abstract
    disjoint-complement-subtype-complemented-subtype-Type-With-Apartness :
      disjoint-subtype
        ( subtype-complemented-subtype-Type-With-Apartness X cA)
        ( complement-subtype-complemented-subtype-Type-With-Apartness X cA)
    disjoint-complement-subtype-complemented-subtype-Type-With-Apartness
      x (x∈A , x∈A') =
      antirefl-apart-Type-With-Apartness X x (A#A' x x x∈A x∈A')
```

### The total subtype associated with a complemented subtype

```agda
module _
  {l1 l2 l : Level}
  (X : Type-With-Apartness l1 l2)
  (cA@(A , A' , A#A') : complemented-subtype-Type-With-Apartness X l)
  where

  is-in-total-subtype-complemented-subtype-Type-With-Apartness :
    type-Type-With-Apartness X → UU l
  is-in-total-subtype-complemented-subtype-Type-With-Apartness x =
    is-in-subtype A x + is-in-subtype A' x

  abstract
    is-prop-is-in-total-subtype-complemented-subtype-Type-With-Apartness :
      (x : type-Type-With-Apartness X) →
      is-prop (is-in-total-subtype-complemented-subtype-Type-With-Apartness x)
    is-prop-is-in-total-subtype-complemented-subtype-Type-With-Apartness x =
      is-prop-coproduct
        ( ev-pair
          ( disjoint-complement-subtype-complemented-subtype-Type-With-Apartness
            ( X)
            ( cA)
            ( x)))
        ( is-prop-is-in-subtype A x)
        ( is-prop-is-in-subtype A' x)

  total-subtype-complemented-subtype-Type-With-Apartness :
    subtype l (type-Type-With-Apartness X)
  total-subtype-complemented-subtype-Type-With-Apartness x =
    ( is-in-total-subtype-complemented-subtype-Type-With-Apartness x ,
      is-prop-is-in-total-subtype-complemented-subtype-Type-With-Apartness x)
```

## References

{{#bibliography}}
