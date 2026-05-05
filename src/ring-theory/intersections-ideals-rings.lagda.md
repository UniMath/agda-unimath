# Intersections of ideals of rings

```agda
module ring-theory.intersections-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.intersections-subtypes
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets

open import ring-theory.ideals-rings
open import ring-theory.poset-of-ideals-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

The
{{#concept "intersection" Disambiguation="of two ideals in a ring" Agda=intersection-ideal-Ring}}
of two [ideals](ring-theory.ideals-rings.md) in a [ring](ring-theory.rings.md)
`R` consists of the elements contained in both of them.

## Definitions

### The universal property of intersections of ideals in rings

```agda
module _
  {l1 l2 l3 : Level} (A : Ring l1)
  (I : ideal-Ring l2 A)
  (J : ideal-Ring l3 A)
  where

  is-intersection-ideal-Ring :
    {l4 : Level} (K : ideal-Ring l4 A) → UUω
  is-intersection-ideal-Ring K =
    is-greatest-binary-lower-bound-Large-Poset
      ( ideal-Ring-Large-Poset A)
      ( I)
      ( J)
      ( K)
```

### Intersections of ideals in rings

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : ideal-Ring l2 R) (J : ideal-Ring l3 R)
  where

  subset-intersection-ideal-Ring : subset-Ring (l2 ⊔ l3) R
  subset-intersection-ideal-Ring =
    intersection-subtype (subset-ideal-Ring R I) (subset-ideal-Ring R J)

  contains-zero-intersection-ideal-Ring :
    contains-zero-subset-Ring R subset-intersection-ideal-Ring
  pr1 contains-zero-intersection-ideal-Ring =
    contains-zero-ideal-Ring R I
  pr2 contains-zero-intersection-ideal-Ring =
    contains-zero-ideal-Ring R J

  is-closed-under-addition-intersection-ideal-Ring :
    is-closed-under-addition-subset-Ring R
      subset-intersection-ideal-Ring
  pr1 (is-closed-under-addition-intersection-ideal-Ring H K) =
    is-closed-under-addition-ideal-Ring R I (pr1 H) (pr1 K)
  pr2 (is-closed-under-addition-intersection-ideal-Ring H K) =
    is-closed-under-addition-ideal-Ring R J (pr2 H) (pr2 K)

  is-closed-under-negatives-intersection-ideal-Ring :
    is-closed-under-negatives-subset-Ring R
      subset-intersection-ideal-Ring
  pr1 (is-closed-under-negatives-intersection-ideal-Ring H) =
    is-closed-under-negatives-ideal-Ring R I (pr1 H)
  pr2 (is-closed-under-negatives-intersection-ideal-Ring H) =
    is-closed-under-negatives-ideal-Ring R J (pr2 H)

  is-closed-under-left-multiplication-intersection-ideal-Ring :
    is-closed-under-left-multiplication-subset-Ring R
      subset-intersection-ideal-Ring
  pr1 (is-closed-under-left-multiplication-intersection-ideal-Ring x y H) =
    is-closed-under-left-multiplication-ideal-Ring R I x y (pr1 H)
  pr2 (is-closed-under-left-multiplication-intersection-ideal-Ring x y H) =
    is-closed-under-left-multiplication-ideal-Ring R J x y (pr2 H)

  is-closed-under-right-multiplication-intersection-ideal-Ring :
    is-closed-under-right-multiplication-subset-Ring R
      subset-intersection-ideal-Ring
  pr1 (is-closed-under-right-multiplication-intersection-ideal-Ring x y H) =
    is-closed-under-right-multiplication-ideal-Ring R I x y (pr1 H)
  pr2 (is-closed-under-right-multiplication-intersection-ideal-Ring x y H) =
    is-closed-under-right-multiplication-ideal-Ring R J x y (pr2 H)

  is-additive-subgroup-intersection-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-intersection-ideal-Ring
  pr1 is-additive-subgroup-intersection-ideal-Ring =
    contains-zero-intersection-ideal-Ring
  pr1 (pr2 is-additive-subgroup-intersection-ideal-Ring) =
    is-closed-under-addition-intersection-ideal-Ring
  pr2 (pr2 is-additive-subgroup-intersection-ideal-Ring) =
    is-closed-under-negatives-intersection-ideal-Ring

  is-ideal-intersection-ideal-Ring :
    is-ideal-subset-Ring R subset-intersection-ideal-Ring
  pr1 is-ideal-intersection-ideal-Ring =
    is-additive-subgroup-intersection-ideal-Ring
  pr1 (pr2 is-ideal-intersection-ideal-Ring) =
    is-closed-under-left-multiplication-intersection-ideal-Ring
  pr2 (pr2 is-ideal-intersection-ideal-Ring) =
    is-closed-under-right-multiplication-intersection-ideal-Ring

  intersection-ideal-Ring : ideal-Ring (l2 ⊔ l3) R
  pr1 intersection-ideal-Ring = subset-intersection-ideal-Ring
  pr2 intersection-ideal-Ring = is-ideal-intersection-ideal-Ring

  is-intersection-intersection-ideal-Ring :
    is-intersection-ideal-Ring R I J intersection-ideal-Ring
  is-intersection-intersection-ideal-Ring K =
    is-greatest-binary-lower-bound-intersection-subtype
      ( subset-ideal-Ring R I)
      ( subset-ideal-Ring R J)
      ( subset-ideal-Ring R K)
```
