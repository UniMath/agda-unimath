# The difference of linear maps between left modules over rings

```agda
module linear-algebra.difference-linear-maps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.addition-linear-maps-left-modules-rings
open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

The
{{#concept "difference" Disambiguation="of linear maps between left modules over rings" Agda=diff-linear-map-left-module-Ring}}
of two [linear maps](linear-algebra.linear-maps-left-modules-rings.md) `f` and
`g` between two [left modules](linear-algebra.left-modules-rings.md) over a
[ring](ring-theory.rings.md) is the linear map `x ↦ f x - g x`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  where

  diff-linear-map-left-module-Ring :
    linear-map-left-module-Ring R M N →
    linear-map-left-module-Ring R M N →
    linear-map-left-module-Ring R M N
  diff-linear-map-left-module-Ring =
    right-subtraction-Ab (ab-add-linear-map-left-module-Ring R M N)
```
