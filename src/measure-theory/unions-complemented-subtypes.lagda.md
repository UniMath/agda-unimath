# Unions of complemented subtypes

```agda
module measure-theory.unions-complemented-subtypes where
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
{{#concept "union" Disambiguation="of two complemented subtypes of a type equipped with an apartness relation" Agda=union-complemented-subtype-Type-With-Apartness}}
of two [complemented subtypes](measure-theory.complemented-subtypes.md)
`(A , A')` and `(B , B')` of a type equipped with an
[apartness relation](foundation.apartness-relations.md) is the pair
`((A ∩ B) ∪ (A ∩ B') ∪ (A' ∩ B), A' ∩ B')`.

This definition follows {{#cite Zeuner22}}.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Type-With-Apartness l1 l2)
  (cA@(A , A' , A#A') : complemented-subtype-Type-With-Apartness X l3)
  (cB@(B , B' , B#B') : complemented-subtype-Type-With-Apartness X l4)
  where

  subtype-union-complemented-subtype-Type-With-Apartness :
    subtype (l3 ⊔ l4) (type-Type-With-Apartness X)
  subtype-union-complemented-subtype-Type-With-Apartness =
    union-subtype
      ( intersection-subtype A' B)
      ( intersection-subtype
        ( A)
        ( total-subtype-complemented-subtype-Type-With-Apartness X cB))

  complement-subtype-union-complemented-subtype-Type-With-Apartness :
    subtype (l3 ⊔ l4) (type-Type-With-Apartness X)
  complement-subtype-union-complemented-subtype-Type-With-Apartness =
    intersection-subtype A' B'

  abstract
    apart-complement-subtype-union-complemented-subtype-Type-With-Apartness :
      apart-subtype-Type-With-Apartness
        ( X)
        ( subtype-union-complemented-subtype-Type-With-Apartness)
        ( complement-subtype-union-complemented-subtype-Type-With-Apartness)
    apart-complement-subtype-union-complemented-subtype-Type-With-Apartness
      x y x∈⟨A∪B⟩ (y∈A' , y∈B') =
      elim-disjunction
        ( rel-apart-Type-With-Apartness X x y)
        ( λ (x∈A' , x∈B) → B#B' x y x∈B y∈B')
        ( λ (x∈A , _) → A#A' x y x∈A y∈A')
        ( x∈⟨A∪B⟩)

  union-complemented-subtype-Type-With-Apartness :
    complemented-subtype-Type-With-Apartness X (l3 ⊔ l4)
  union-complemented-subtype-Type-With-Apartness =
    ( subtype-union-complemented-subtype-Type-With-Apartness ,
      complement-subtype-union-complemented-subtype-Type-With-Apartness ,
      apart-complement-subtype-union-complemented-subtype-Type-With-Apartness)
```

## References

{{#bibliography}}
