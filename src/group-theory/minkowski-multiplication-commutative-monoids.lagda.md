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
open import foundation.inhabited-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.minkowski-multiplication-monoids
open import group-theory.monoids
open import group-theory.subsets-commutative-monoids
```

</details>

## Idea

For two [subsets](group-theory.subsets-commutative-monoids.md) `A`, `B` of a
[commutative monoid](group-theory.commutative-monoids.md) `M`, the Minkowski
multiplication of `A` and `B` is the set of elements that can be formed by
multiplying an element of `A` and an element of `B`. (This is more usually
referred to as a Minkowski sum, but as the operation on commutative monoids is
referred to as `mul`, we use multiplicative terminology.)

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (M : Commutative-Monoid l1)
  (A : subset-Commutative-Monoid l2 M)
  (B : subset-Commutative-Monoid l3 M)
  where

  minkowski-mul-Commutative-Monoid :
    subset-Commutative-Monoid (l1 ⊔ l2 ⊔ l3) M
  minkowski-mul-Commutative-Monoid =
    minkowski-mul-Monoid (monoid-Commutative-Monoid M) A B
```

## Properties

### Minkowski multiplication on a commutative monoid is commutative

```agda
module _
  {l1 l2 l3 : Level}
  (M : Commutative-Monoid l1)
  (A : subset-Commutative-Monoid l2 M)
  (B : subset-Commutative-Monoid l3 M)
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
  (A : subset-Commutative-Monoid l2 M)
  (B : subset-Commutative-Monoid l3 M)
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

### The Minkowski multiplication of two inhabited subsets of a commutative monoid is inhabited

```agda
module _
  {l1 : Level}
  (M : Commutative-Monoid l1)
  where

  minkowski-mul-inhabited-is-inhabited-Commutative-Monoid :
    {l2 l3 : Level} →
    (A : subset-Commutative-Monoid l2 M) →
    (B : subset-Commutative-Monoid l3 M) →
    is-inhabited-subtype A →
    is-inhabited-subtype B →
    is-inhabited-subtype (minkowski-mul-Commutative-Monoid M A B)
  minkowski-mul-inhabited-is-inhabited-Commutative-Monoid =
    minkowski-mul-inhabited-is-inhabited-Monoid (monoid-Commutative-Monoid M)
```

## See also

- Minkowski multiplication on semigroups is defined in
  [`group-theory.minkowski-multiplication-semigroups`](group-theory.minkowski-multiplication-semigroups.md).
- Minkowski multiplication on monoids is defined in
  [`group-theory.minkowski-multiplication-monoids`](group-theory.minkowski-multiplication-monoids.md).

## External links

- [Minkowski addition](https://en.wikipedia.org/wiki/Minkowski_addition) at
  Wikipedia
