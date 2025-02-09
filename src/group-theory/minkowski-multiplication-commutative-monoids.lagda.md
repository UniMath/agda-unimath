# Minkowski multiplication of commutative monoid subtypes

```agda
module group-theory.minkowski-multiplication-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.powersets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.minkowski-multiplication-monoids
open import group-theory.commutative-monoids
open import group-theory.monoids
```

</details>

## Idea

For two [subtypes](foundation-core.subtypes.md) `A`, `B` of a
[commutative monoid](group-theory.commutative-monoids.md) `M`, the Minkowski multiplication of
`A` and `B` is the set of elements that can be formed by multiplying an element
of `A` and an element of `B`. (This is more usually referred to as a Minkowski
sum, but as the operation on commutative monoids is referred to as `mul`, we use
multiplicative terminology.)

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (M : Commutative-Monoid l1)
  (A : subtype l2 (type-Commutative-Monoid M))
  (B : subtype l3 (type-Commutative-Monoid M))
  where

  minkowski-mul-Commutative-Monoid :
    subtype (l1 ⊔ l2 ⊔ l3) (type-Commutative-Monoid M)
  minkowski-mul-Commutative-Monoid =
    minkowski-mul-Monoid (monoid-Commutative-Monoid M) A B
```

## Properties

### Minkowski multiplication on a commutative monoid is commutative

```agda
module _
  {l1 l2 l3 : Level}
  (M : Commutative-Monoid l1)
  (A : subtype l2 (type-Commutative-Monoid M))
  (B : subtype l3 (type-Commutative-Monoid M))
  where

  commutative-minkowski-mul-leq-Commutative-Monoid :
    minkowski-mul-Commutative-Monoid M A B ⊆
    minkowski-mul-Commutative-Monoid M B A
  commutative-minkowski-mul-leq-Commutative-Monoid x =
    elim-exists
      (minkowski-mul-Commutative-Monoid M B A x)
      ( λ (a , b) (a∈A , b∈B , x=ab) →
        intro-exists
          ( b , a)
          ( b∈B , a∈A , x=ab ∙ commutative-mul-Commutative-Monoid M a b))

module _
  {l1 l2 l3 : Level}
  (M : Commutative-Monoid l1)
  (A : subtype l2 (type-Commutative-Monoid M))
  (B : subtype l3 (type-Commutative-Monoid M))
  where

  commutative-minkowski-mul-Commutative-Monoid :
    minkowski-mul-Commutative-Monoid M A B ＝
    minkowski-mul-Commutative-Monoid M B A
  commutative-minkowski-mul-Commutative-Monoid =
    antisymmetric-sim-subtype
      ( minkowski-mul-Commutative-Monoid M A B)
      ( minkowski-mul-Commutative-Monoid M B A)
      ( commutative-minkowski-mul-leq-Commutative-Monoid M A B ,
        commutative-minkowski-mul-leq-Commutative-Monoid M B A)
```

### Minkowski multiplication on a commutative monoid is a commutative monoid

```agda
module _
  {l : Level}
  (M : Commutative-Monoid l)
  where

  commutative-monoid-minkowski-mul-Commutative-Monoid :
    Commutative-Monoid (lsuc l)
  pr1 commutative-monoid-minkowski-mul-Commutative-Monoid =
    monoid-minkowski-mul-Monoid (monoid-Commutative-Monoid M)
  pr2 commutative-monoid-minkowski-mul-Commutative-Monoid =
    commutative-minkowski-mul-Commutative-Monoid M
```

## See also

- Minkowski multiplication on semigroups is defined in
  [`group-theory.minkowski-multiplication-semigroups`](group-theory.minkowski-multiplication-semigroups.md).
- Minkowski multiplication on monoids is defined in
  [`group-theory.minkowski-multiplication-monoids`](group-theory.minkowski-multiplication-monoids.md).

## External links

- [Minkowski addition](https://en.wikipedia.org/wiki/Minkowski_addition) at
  Wikipedia
