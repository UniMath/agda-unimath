# Intersections of left ideals of semirings

```agda
module ring-theory.intersections-left-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.intersections-subtypes
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets

open import ring-theory.left-ideals-semirings
open import ring-theory.poset-of-left-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

The
{{#concept "intersection" Disambiguation="of two left ideals in a semiring" Agda=intersection-left-ideal-Semiring}}
of two [left ideals](ring-theory.left-ideals-semirings.md) in a
[semiring](ring-theory.semirings.md) `R` consists of the elements contained in
both of them.

## Definitions

### The universal property of the intersection of two left ideals in a semiring

```agda
module _
  {l1 l2 l3 : Level} (A : Semiring l1)
  (I : left-ideal-Semiring l2 A)
  (J : left-ideal-Semiring l3 A)
  where

  is-intersection-left-ideal-Semiring :
    {l4 : Level} (K : left-ideal-Semiring l4 A) → UUω
  is-intersection-left-ideal-Semiring K =
    is-greatest-binary-lower-bound-Large-Poset
      ( left-ideal-Semiring-Large-Poset A)
      ( I)
      ( J)
      ( K)
```

### The intersection of two left ideals in a semiring

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (A : left-ideal-Semiring l2 R) (B : left-ideal-Semiring l3 R)
  where

  subset-intersection-left-ideal-Semiring : subset-Semiring (l2 ⊔ l3) R
  subset-intersection-left-ideal-Semiring =
    intersection-subtype
      ( subset-left-ideal-Semiring R A)
      ( subset-left-ideal-Semiring R B)

  contains-zero-intersection-left-ideal-Semiring :
    contains-zero-subset-Semiring R subset-intersection-left-ideal-Semiring
  pr1 contains-zero-intersection-left-ideal-Semiring =
    contains-zero-left-ideal-Semiring R A
  pr2 contains-zero-intersection-left-ideal-Semiring =
    contains-zero-left-ideal-Semiring R B

  is-closed-under-addition-intersection-left-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R
      subset-intersection-left-ideal-Semiring
  pr1 (is-closed-under-addition-intersection-left-ideal-Semiring H K) =
    is-closed-under-addition-left-ideal-Semiring R A (pr1 H) (pr1 K)
  pr2 (is-closed-under-addition-intersection-left-ideal-Semiring H K) =
    is-closed-under-addition-left-ideal-Semiring R B (pr2 H) (pr2 K)

  is-closed-under-left-multiplication-intersection-left-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      subset-intersection-left-ideal-Semiring
  pr1 (is-closed-under-left-multiplication-intersection-left-ideal-Semiring H) =
    is-closed-under-left-multiplication-left-ideal-Semiring R A (pr1 H)
  pr2 (is-closed-under-left-multiplication-intersection-left-ideal-Semiring H) =
    is-closed-under-left-multiplication-left-ideal-Semiring R B (pr2 H)

  is-left-ideal-intersection-left-ideal-Semiring :
    is-left-ideal-subset-Semiring R subset-intersection-left-ideal-Semiring
  pr1 (pr1 is-left-ideal-intersection-left-ideal-Semiring) =
    contains-zero-intersection-left-ideal-Semiring
  pr2 (pr1 is-left-ideal-intersection-left-ideal-Semiring) =
    is-closed-under-addition-intersection-left-ideal-Semiring
  pr2 is-left-ideal-intersection-left-ideal-Semiring =
    is-closed-under-left-multiplication-intersection-left-ideal-Semiring

  intersection-left-ideal-Semiring :
    left-ideal-Semiring (l2 ⊔ l3) R
  pr1 intersection-left-ideal-Semiring =
    subset-intersection-left-ideal-Semiring
  pr2 intersection-left-ideal-Semiring =
    is-left-ideal-intersection-left-ideal-Semiring

  is-intersection-intersection-left-ideal-Semiring :
    is-intersection-left-ideal-Semiring R A B intersection-left-ideal-Semiring
  is-intersection-intersection-left-ideal-Semiring C =
    is-intersection-intersection-subtype
      ( subset-left-ideal-Semiring R A)
      ( subset-left-ideal-Semiring R B)
      ( subset-left-ideal-Semiring R C)
```
