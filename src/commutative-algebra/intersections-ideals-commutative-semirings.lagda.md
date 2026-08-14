# Intersections of ideals of commutative semirings

```agda
module commutative-algebra.intersections-ideals-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.ideals-commutative-semirings
open import commutative-algebra.commutative-semirings
open import commutative-algebra.poset-of-ideals-commutative-semirings
open import commutative-algebra.subsets-commutative-semirings

open import foundation.dependent-pair-types
open import foundation.intersections-subtypes
open import foundation.universe-levels

open import ring-theory.intersections-left-ideals-semirings
```

</details>

## Idea

The
{{#concept "intersection" Disambiguation="of two ideals in a commutative semiring" Agda=intersection-ideal-Commutative-Semiring}}
of two [ideals](ring-theory.ideals-semirings.md) in a
[semiring](ring-theory.semirings.md) `R` consists of the elements contained in
both of them.

## Definitions

### The universal property of the intersection of two ideals in a commutative semiring

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Semiring l1)
  (I : ideal-Commutative-Semiring l2 A)
  (J : ideal-Commutative-Semiring l3 A)
  where

  is-intersection-ideal-Commutative-Semiring :
    {l4 : Level} (K : ideal-Commutative-Semiring l4 A) → UUω
  is-intersection-ideal-Commutative-Semiring =
    is-intersection-left-ideal-Semiring (semiring-Commutative-Semiring A) I J
```

### The intersection of two ideals in a commutative semiring

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  (A : ideal-Commutative-Semiring l2 R) (B : ideal-Commutative-Semiring l3 R)
  where

  subset-intersection-ideal-Commutative-Semiring :
    subset-Commutative-Semiring (l2 ⊔ l3) R
  subset-intersection-ideal-Commutative-Semiring =
    subset-intersection-left-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( A)
      ( B)

  contains-zero-intersection-ideal-Commutative-Semiring :
    contains-zero-subset-Commutative-Semiring R
      subset-intersection-ideal-Commutative-Semiring
  contains-zero-intersection-ideal-Commutative-Semiring =
    contains-zero-intersection-left-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( A)
      ( B)

  is-closed-under-addition-intersection-ideal-Commutative-Semiring :
    is-closed-under-addition-subset-Commutative-Semiring R
      subset-intersection-ideal-Commutative-Semiring
  is-closed-under-addition-intersection-ideal-Commutative-Semiring =
    is-closed-under-addition-intersection-left-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( A)
      ( B)

  is-closed-under-left-multiplication-intersection-ideal-Commutative-Semiring :
    is-closed-under-left-multiplication-subset-Commutative-Semiring R
      subset-intersection-ideal-Commutative-Semiring
  is-closed-under-left-multiplication-intersection-ideal-Commutative-Semiring =
    is-closed-under-left-multiplication-intersection-left-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( A)
      ( B)

  is-ideal-intersection-ideal-Commutative-Semiring :
    is-ideal-subset-Commutative-Semiring R
      subset-intersection-ideal-Commutative-Semiring
  is-ideal-intersection-ideal-Commutative-Semiring =
    is-left-ideal-intersection-left-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( A)
      ( B)

  intersection-ideal-Commutative-Semiring :
    ideal-Commutative-Semiring (l2 ⊔ l3) R
  intersection-ideal-Commutative-Semiring =
    intersection-left-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( A)
      ( B)

  is-intersection-intersection-ideal-Commutative-Semiring :
    is-intersection-ideal-Commutative-Semiring R A B
      intersection-ideal-Commutative-Semiring
  is-intersection-intersection-ideal-Commutative-Semiring =
    is-intersection-intersection-left-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( A)
      ( B)
```
