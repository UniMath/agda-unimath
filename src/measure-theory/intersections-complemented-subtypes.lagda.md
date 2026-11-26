# Intersections of complemented subtypes

```agda
module measure-theory.intersections-complemented-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.intersections-subtypes
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import measure-theory.apart-subtypes
open import measure-theory.complemented-subtypes
```

</details>

## Idea

The
{{#concept "intersection" Disambiguation="of two complemented subtypes of a type equipped with an apartness relation" Agda=intersection-complemented-subtype-Type-With-Apartness}}
of two [complemented subtypes](measure-theory.complemented-subtypes.md)
`(A , A')` and `(B , B')` of a type equipped with an
[apartness relation](foundation.apartness-relations.md) is the pair
`(A ∩ B , (A ∩ B') ∪ (A' ∩ B) ∪ (A' ∩ B'))`.

This definition follows {{#cite Zeuner22}}.

## Definition

### Intersection of two complemented subtypes

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Type-With-Apartness l1 l2)
  (cA@(A , A' , A#A') : complemented-subtype-Type-With-Apartness X l3)
  (cB@(B , B' , B#B') : complemented-subtype-Type-With-Apartness X l4)
  where

  subtype-intersection-complemented-subtype-Type-With-Apartness :
    subtype (l3 ⊔ l4) (type-Type-With-Apartness X)
  subtype-intersection-complemented-subtype-Type-With-Apartness =
    intersection-subtype A B

  complement-subtype-intersection-complemented-subtype-Type-With-Apartness :
    subtype (l3 ⊔ l4) (type-Type-With-Apartness X)
  complement-subtype-intersection-complemented-subtype-Type-With-Apartness =
    union-subtype
      ( intersection-subtype A B')
      ( intersection-subtype
        ( A')
        ( total-subtype-complemented-subtype-Type-With-Apartness X cB))

  abstract
    apart-complement-subtype-intersection-complemented-subtype-Type-With-Apartness :
      apart-subtype-Type-With-Apartness
        ( X)
        ( subtype-intersection-complemented-subtype-Type-With-Apartness)
        ( complement-subtype-intersection-complemented-subtype-Type-With-Apartness)
    apart-complement-subtype-intersection-complemented-subtype-Type-With-Apartness
      x y (x∈A , x∈B) =
      elim-disjunction
        ( rel-apart-Type-With-Apartness X x y)
        ( λ (y∈A , y∈B') → B#B' x y x∈B y∈B')
        ( λ (y∈A' , _) → A#A' x y x∈A y∈A')

  intersection-complemented-subtype-Type-With-Apartness :
    complemented-subtype-Type-With-Apartness X (l3 ⊔ l4)
  intersection-complemented-subtype-Type-With-Apartness =
    ( subtype-intersection-complemented-subtype-Type-With-Apartness ,
      complement-subtype-intersection-complemented-subtype-Type-With-Apartness ,
      apart-complement-subtype-intersection-complemented-subtype-Type-With-Apartness)
```

## References

{{#bibliography}}
