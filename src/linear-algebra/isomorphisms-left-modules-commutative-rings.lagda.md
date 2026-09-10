# Isomorphisms of left modules over commutative rings

```agda
module linear-algebra.isomorphisms-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.isomorphisms-left-modules-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
```

</details>

## Idea

{{#concept "Isomorphisms" Disambiguation="of left modules over a commutative ring" Agda=iso-left-module-Commutative-Ring}}
of [left modules](linear-algebra.left-modules-commutative-rings.md) over a
[commutative ring](commutative-algebra.commutative-rings.md) are
[linear maps](linear-algebra.linear-maps-left-modules-commutative-rings.md) that
have a two-sided inverse.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  is-iso-prop-left-module-Commutative-Ring :
    subtype (l1 ⊔ l2 ⊔ l3) (linear-map-left-module-Commutative-Ring R M N)
  is-iso-prop-left-module-Commutative-Ring =
    is-iso-prop-left-module-Ring (ring-Commutative-Ring R) M N

  is-iso-left-module-Commutative-Ring :
    linear-map-left-module-Commutative-Ring R M N → UU (l1 ⊔ l2 ⊔ l3)
  is-iso-left-module-Commutative-Ring =
    is-in-subtype is-iso-prop-left-module-Commutative-Ring

  iso-left-module-Commutative-Ring : UU (l1 ⊔ l2 ⊔ l3)
  iso-left-module-Commutative-Ring =
    type-subtype is-iso-prop-left-module-Commutative-Ring

  linear-map-iso-left-module-Commutative-Ring :
    iso-left-module-Commutative-Ring →
    linear-map-left-module-Commutative-Ring R M N
  linear-map-iso-left-module-Commutative-Ring = pr1

  is-iso-linear-map-iso-left-module-Commutative-Ring :
    (i : iso-left-module-Commutative-Ring) →
    is-iso-left-module-Commutative-Ring
      ( linear-map-iso-left-module-Commutative-Ring i)
  is-iso-linear-map-iso-left-module-Commutative-Ring = pr2

module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  (f : iso-left-module-Commutative-Ring R M N)
  where

  inv-iso-left-module-Commutative-Ring : iso-left-module-Commutative-Ring R N M
  inv-iso-left-module-Commutative-Ring =
    inv-iso-left-module-Ring (ring-Commutative-Ring R) M N f

  linear-map-inv-iso-left-module-Commutative-Ring :
    linear-map-left-module-Commutative-Ring R N M
  linear-map-inv-iso-left-module-Commutative-Ring =
    linear-map-inv-iso-left-module-Ring (ring-Commutative-Ring R) M N f
```
