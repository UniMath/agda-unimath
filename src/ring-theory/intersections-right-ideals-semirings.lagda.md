# Intersections of right ideals of semirings

```agda
module ring-theory.intersections-right-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.intersections-subtypes
open import foundation.universe-levels

open import ring-theory.right-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

The
{{#concept "intersection" Disambiguation="of two right ideals in a semiring" Agda=intersection-right-ideal-Semiring}}
of two [right ideals](ring-theory.right-ideals-semirings.md) in a
[semiring](ring-theory.semirings.md) `R` consists of the elements contained in
both of them.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (A : right-ideal-Semiring l2 R) (B : right-ideal-Semiring l3 R)
  where

  subset-intersection-right-ideal-Semiring : subset-Semiring (l2 ⊔ l3) R
  subset-intersection-right-ideal-Semiring =
    intersection-subtype
      ( subset-right-ideal-Semiring R A)
      ( subset-right-ideal-Semiring R B)

  contains-zero-intersection-right-ideal-Semiring :
    contains-zero-subset-Semiring R subset-intersection-right-ideal-Semiring
  pr1 contains-zero-intersection-right-ideal-Semiring =
    contains-zero-right-ideal-Semiring R A
  pr2 contains-zero-intersection-right-ideal-Semiring =
    contains-zero-right-ideal-Semiring R B

  is-closed-under-addition-intersection-right-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R
      subset-intersection-right-ideal-Semiring
  pr1 (is-closed-under-addition-intersection-right-ideal-Semiring H K) =
    is-closed-under-addition-right-ideal-Semiring R A (pr1 H) (pr1 K)
  pr2 (is-closed-under-addition-intersection-right-ideal-Semiring H K) =
    is-closed-under-addition-right-ideal-Semiring R B (pr2 H) (pr2 K)

  is-closed-under-right-multiplication-intersection-right-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-intersection-right-ideal-Semiring
  pr1 (is-closed-under-right-multiplication-intersection-right-ideal-Semiring H) =
    is-closed-under-right-multiplication-right-ideal-Semiring R A (pr1 H)
  pr2 (is-closed-under-right-multiplication-intersection-right-ideal-Semiring H) =
    is-closed-under-right-multiplication-right-ideal-Semiring R B (pr2 H)

  is-right-ideal-intersection-right-ideal-Semiring :
    is-right-ideal-subset-Semiring R subset-intersection-right-ideal-Semiring
  pr1 (pr1 is-right-ideal-intersection-right-ideal-Semiring) =
    contains-zero-intersection-right-ideal-Semiring
  pr2 (pr1 is-right-ideal-intersection-right-ideal-Semiring) =
    is-closed-under-addition-intersection-right-ideal-Semiring
  pr2 is-right-ideal-intersection-right-ideal-Semiring =
    is-closed-under-right-multiplication-intersection-right-ideal-Semiring

  intersection-right-ideal-Semiring :
    right-ideal-Semiring (l2 ⊔ l3) R
  pr1 intersection-right-ideal-Semiring =
    subset-intersection-right-ideal-Semiring
  pr2 intersection-right-ideal-Semiring =
    is-right-ideal-intersection-right-ideal-Semiring
```
