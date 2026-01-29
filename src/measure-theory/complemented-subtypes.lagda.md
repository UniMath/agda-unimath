# Complemented subtypes

```agda
module measure-theory.complemented-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.dependent-pair-types
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
[subtypes](foundation-core.subtypes.md) `A` and `A'` of `X` such that every
element of `A` is apart from every element of `A'`.

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

  subtype-complemented-subtype-Type-With-Apartness :
    {l : Level} → complemented-subtype-Type-With-Apartness l →
    subtype l (type-Type-With-Apartness X)
  subtype-complemented-subtype-Type-With-Apartness (A , _ , _) = A

  complement-subtype-complemented-subtype-Type-With-Apartness :
    {l : Level} → complemented-subtype-Type-With-Apartness l →
    subtype l (type-Type-With-Apartness X)
  complement-subtype-complemented-subtype-Type-With-Apartness (_ , A' , _) = A'

  apart-subtype-complemented-subtype-Type-With-Apartness :
    {l : Level} (A : complemented-subtype-Type-With-Apartness l) →
    apart-subtype-Type-With-Apartness
      ( X)
      ( subtype-complemented-subtype-Type-With-Apartness A)
      ( complement-subtype-complemented-subtype-Type-With-Apartness A)
  apart-subtype-complemented-subtype-Type-With-Apartness (_ , _ , A#A') = A#A'
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
