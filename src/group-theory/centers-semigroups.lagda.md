# Center of a semigroup

```agda
module group-theory.centers-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.central-elements-semigroups
open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
open import group-theory.subsemigroups
```

</details>

## Idea

The center of a semigroup consists of those elements that are central.

## Definition

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  subtype-center-Semigroup : type-Semigroup G → Prop l
  subtype-center-Semigroup = is-central-element-prop-Semigroup G

  center-Semigroup : Subsemigroup l G
  pr1 center-Semigroup = subtype-center-Semigroup
  pr2 center-Semigroup {x} {y} = is-central-element-mul-Semigroup G x y

  semigroup-center-Semigroup : Semigroup l
  semigroup-center-Semigroup = semigroup-Subsemigroup G center-Semigroup

  type-center-Semigroup : UU l
  type-center-Semigroup =
    type-Subsemigroup G center-Semigroup

  mul-center-Semigroup :
    (x y : type-center-Semigroup) → type-center-Semigroup
  mul-center-Semigroup = mul-Subsemigroup G center-Semigroup

  associative-mul-center-Semigroup :
    (x y z : type-center-Semigroup) →
    mul-center-Semigroup (mul-center-Semigroup x y) z ＝
    mul-center-Semigroup x (mul-center-Semigroup y z)
  associative-mul-center-Semigroup =
    associative-mul-Subsemigroup G center-Semigroup

  inclusion-center-Semigroup :
    type-center-Semigroup → type-Semigroup G
  inclusion-center-Semigroup =
    inclusion-Subsemigroup G center-Semigroup

  preserves-mul-inclusion-center-Semigroup :
    {x y : type-center-Semigroup} →
    inclusion-center-Semigroup (mul-center-Semigroup x y) ＝
    mul-Semigroup G
      ( inclusion-center-Semigroup x)
      ( inclusion-center-Semigroup y)
  preserves-mul-inclusion-center-Semigroup {x} {y} =
    preserves-mul-inclusion-Subsemigroup G center-Semigroup {x} {y}

  hom-inclusion-center-Semigroup :
    hom-Semigroup semigroup-center-Semigroup G
  hom-inclusion-center-Semigroup =
    hom-inclusion-Subsemigroup G center-Semigroup
```
