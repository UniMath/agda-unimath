# Minkowski multiplication of monoid subtypes

```agda
module group-theory.minkowski-multiplication-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.powersets
open import foundation.unital-binary-operations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.minkowski-multiplication-semigroups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

For two [subtypes](foundation-core.subtypes.md) `A`, `B` of a
[monoid](group-theory.monoids.md) `M`, the Minkowski multiplication of
`A` and `B` is the set of elements that can be formed by multiplying an element
of `A` and an element of `B`. (This is more usually referred to as a Minkowski
sum, but as the operation on monoids is referred to as `mul`, we use
multiplicative terminology.)

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (M : Monoid l1)
  (A : subtype l2 (type-Monoid M))
  (B : subtype l3 (type-Monoid M))
  where

  minkowski-mul-Monoid : subtype (l1 ⊔ l2 ⊔ l3) (type-Monoid M)
  minkowski-mul-Monoid = minkowski-mul-Semigroup (semigroup-Monoid M) A B
```

## Properties

### Unit laws for Minkowski multiplication of semigroup subtypes

```agda
module _
  {l1 l2 : Level}
  (M : Monoid l1)
  (A : subtype l2 (type-Monoid M))
  where

  left-unit-law-minkowski-mul-Monoid :
    sim-subtype (minkowski-mul-Monoid M (is-unit-Monoid-Prop M) A) A
  pr1 left-unit-law-minkowski-mul-Monoid a =
    elim-exists
      ( A a)
      ( λ (z , a') (z=1 , a'∈A , a=za') →
        tr
          ( is-in-subtype A)
          ( inv
            ( equational-reasoning
              a
              ＝ mul-Monoid M z a' by a=za'
              ＝ mul-Monoid M (unit-Monoid M) a' by ap (mul-Monoid' M a') z=1
              ＝ a' by left-unit-law-mul-Monoid M a'))
          ( a'∈A))
  pr2 left-unit-law-minkowski-mul-Monoid a a∈A =
    intro-exists
      ( unit-Monoid M , a)
      ( refl , a∈A , inv (left-unit-law-mul-Monoid M a))

  right-unit-law-minkowski-mul-Monoid :
    sim-subtype (minkowski-mul-Monoid M A (is-unit-Monoid-Prop M)) A
  pr1 right-unit-law-minkowski-mul-Monoid a =
    elim-exists
      ( A a)
      ( λ (a' , z) (a'∈A , z=1 , a=a'z) →
        tr
          ( is-in-subtype A)
          ( inv
            ( equational-reasoning
              a
              ＝ mul-Monoid M a' z by a=a'z
              ＝ mul-Monoid M a' (unit-Monoid M) by ap (mul-Monoid M a') z=1
              ＝ a' by right-unit-law-mul-Monoid M a'))
          ( a'∈A))
  pr2 right-unit-law-minkowski-mul-Monoid a a∈A =
    intro-exists
      ( a , unit-Monoid M)
      ( a∈A , refl , inv (right-unit-law-mul-Monoid M a))
```

### Minkowski multiplication of subtypes of a monoid forms a monoid

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  is-unital-minkowski-mul-Monoid :
    is-unital (minkowski-mul-Monoid {l} {l} {l} M)
  pr1 is-unital-minkowski-mul-Monoid = is-unit-Monoid-Prop M
  pr1 (pr2 is-unital-minkowski-mul-Monoid) A =
    antisymmetric-sim-subtype
      ( minkowski-mul-Monoid M (is-unit-Monoid-Prop M) A)
      ( A)
      ( left-unit-law-minkowski-mul-Monoid M A)
  pr2 (pr2 is-unital-minkowski-mul-Monoid) A =
    antisymmetric-sim-subtype
      ( minkowski-mul-Monoid M A (is-unit-Monoid-Prop M))
      ( A)
      ( right-unit-law-minkowski-mul-Monoid M A)

  monoid-minkowski-mul-Monoid : Monoid (lsuc l)
  pr1 monoid-minkowski-mul-Monoid =
    semigroup-minkowski-mul-Semigroup (semigroup-Monoid M)
  pr2 monoid-minkowski-mul-Monoid = is-unital-minkowski-mul-Monoid
```

## See also

- Minkowski multiplication on semigroups is defined in
  [`group-theory.minkowski-multiplication-semigroups`](group-theory.minkowski-multiplication-semigroups.md).

## External links

- [Minkowski addition](https://en.wikipedia.org/wiki/Minkowski_addition) at
  Wikipedia
