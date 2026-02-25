# Intersections of ideals of semirings

```agda
module ring-theory.intersections-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.intersections-subtypes
open import foundation.universe-levels

open import ring-theory.ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

The
{{#concept "intersection" Disambiguation="of two ideals in a semiring" Agda=intersection-ideal-Semiring}}
of two [ideals](ring-theory.ideals-semirings.md) in a
[semiring](ring-theory.semirings.md) `R` consists of the elements contained in
both of them.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (A : ideal-Semiring l2 R) (B : ideal-Semiring l3 R)
  where

  subset-intersection-ideal-Semiring : subset-Semiring (l2 ⊔ l3) R
  subset-intersection-ideal-Semiring =
    intersection-subtype
      ( subset-ideal-Semiring R A)
      ( subset-ideal-Semiring R B)

  contains-zero-intersection-ideal-Semiring :
    contains-zero-subset-Semiring R subset-intersection-ideal-Semiring
  pr1 contains-zero-intersection-ideal-Semiring =
    contains-zero-ideal-Semiring R A
  pr2 contains-zero-intersection-ideal-Semiring =
    contains-zero-ideal-Semiring R B

  is-closed-under-addition-intersection-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R
      subset-intersection-ideal-Semiring
  pr1 (is-closed-under-addition-intersection-ideal-Semiring x y H K) =
    is-closed-under-addition-ideal-Semiring R A x y (pr1 H) (pr1 K)
  pr2 (is-closed-under-addition-intersection-ideal-Semiring x y H K) =
    is-closed-under-addition-ideal-Semiring R B x y (pr2 H) (pr2 K)

  is-closed-under-left-multiplication-intersection-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      subset-intersection-ideal-Semiring
  pr1 (is-closed-under-left-multiplication-intersection-ideal-Semiring x y H) =
    is-closed-under-left-multiplication-ideal-Semiring R A x y (pr1 H)
  pr2 (is-closed-under-left-multiplication-intersection-ideal-Semiring x y H) =
    is-closed-under-left-multiplication-ideal-Semiring R B x y (pr2 H)

  is-closed-under-right-multiplication-intersection-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-intersection-ideal-Semiring
  pr1 (is-closed-under-right-multiplication-intersection-ideal-Semiring x y H) =
    is-closed-under-right-multiplication-ideal-Semiring R A x y (pr1 H)
  pr2 (is-closed-under-right-multiplication-intersection-ideal-Semiring x y H) =
    is-closed-under-right-multiplication-ideal-Semiring R B x y (pr2 H)

  is-ideal-intersection-ideal-Semiring :
    is-ideal-subset-Semiring R subset-intersection-ideal-Semiring
  pr1 (pr1 is-ideal-intersection-ideal-Semiring) =
    contains-zero-intersection-ideal-Semiring
  pr2 (pr1 is-ideal-intersection-ideal-Semiring) =
    is-closed-under-addition-intersection-ideal-Semiring
  pr1 (pr2 is-ideal-intersection-ideal-Semiring) =
    is-closed-under-left-multiplication-intersection-ideal-Semiring
  pr2 (pr2 is-ideal-intersection-ideal-Semiring) =
    is-closed-under-right-multiplication-intersection-ideal-Semiring

  intersection-ideal-Semiring : ideal-Semiring (l2 ⊔ l3) R
  pr1 intersection-ideal-Semiring = subset-intersection-ideal-Semiring
  pr2 intersection-ideal-Semiring = is-ideal-intersection-ideal-Semiring
```
