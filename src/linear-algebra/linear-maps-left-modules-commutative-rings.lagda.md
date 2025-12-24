# Linear maps on left modules over commutative rings

```agda
module linear-algebra.linear-maps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-rings
```

</details>

## Idea

A
{{#concept "linear map" Disambiguation="between left modules over commutative rings" Disambiguation=linear-map-left-module-Commutative-Ring}}
from a [left module](linear-algebra.left-modules-commutative-rings.md) `M` over
a [commutative ring](commutative-algebra.commutative-rings.md) `R` to another
left module `N` over `R` is a map `f` with the following properties:

- Additivity: `f (a + b) = f a + f b`
- Homogeneity: `f (c * a) = c * f a`

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (V : left-module-Commutative-Ring l2 R)
  (W : left-module-Commutative-Ring l3 R)
  (f :
    type-left-module-Commutative-Ring R V →
    type-left-module-Commutative-Ring R W)
  where

  is-additive-map-prop-left-module-Commutative-Ring : Prop (l2 ⊔ l3)
  is-additive-map-prop-left-module-Commutative-Ring =
    is-additive-map-prop-left-module-Ring
      ( ring-Commutative-Ring R)
      ( V)
      ( W)
      ( f)

  is-additive-map-left-module-Commutative-Ring : UU (l2 ⊔ l3)
  is-additive-map-left-module-Commutative-Ring =
    type-Prop is-additive-map-prop-left-module-Commutative-Ring

  is-homogeneous-map-prop-left-module-Commutative-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-homogeneous-map-prop-left-module-Commutative-Ring =
    is-homogeneous-map-prop-left-module-Ring
      ( ring-Commutative-Ring R)
      ( V)
      ( W)
      ( f)

  is-homogeneous-map-left-module-Commutative-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-homogeneous-map-left-module-Commutative-Ring =
    type-Prop is-homogeneous-map-prop-left-module-Commutative-Ring

  is-linear-map-prop-left-module-Commutative-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-linear-map-prop-left-module-Commutative-Ring =
    is-linear-map-prop-left-module-Ring
      ( ring-Commutative-Ring R)
      ( V)
      ( W)
      ( f)

  is-linear-map-left-module-Commutative-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-linear-map-left-module-Commutative-Ring =
    type-Prop is-linear-map-prop-left-module-Commutative-Ring

linear-map-left-module-Commutative-Ring :
  {l1 l2 l3 : Level} (R : Commutative-Ring l1) →
  left-module-Commutative-Ring l2 R → left-module-Commutative-Ring l3 R →
  UU (l1 ⊔ l2 ⊔ l3)
linear-map-left-module-Commutative-Ring R V W =
  type-subtype (is-linear-map-prop-left-module-Commutative-Ring R V W)

module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (V : left-module-Commutative-Ring l2 R)
  (W : left-module-Commutative-Ring l3 R)
  (f : linear-map-left-module-Commutative-Ring R V W)
  where

  map-linear-map-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring R V →
    type-left-module-Commutative-Ring R W
  map-linear-map-left-module-Commutative-Ring = pr1 f

  is-linear-map-linear-map-left-module-Commutative-Ring :
    is-linear-map-left-module-Commutative-Ring R V W
      ( map-linear-map-left-module-Commutative-Ring)
  is-linear-map-linear-map-left-module-Commutative-Ring = pr2 f

  is-additive-map-linear-map-left-module-Commutative-Ring :
    is-additive-map-left-module-Commutative-Ring R V W
      ( map-linear-map-left-module-Commutative-Ring)
  is-additive-map-linear-map-left-module-Commutative-Ring =
    pr1 is-linear-map-linear-map-left-module-Commutative-Ring

  is-homogeneous-map-linear-map-left-module-Commutative-Ring :
    is-homogeneous-map-left-module-Commutative-Ring R V W
      ( map-linear-map-left-module-Commutative-Ring)
  is-homogeneous-map-linear-map-left-module-Commutative-Ring =
    pr2 is-linear-map-linear-map-left-module-Commutative-Ring
```

## Properties

### A linear map maps zero to zero

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (V : left-module-Commutative-Ring l2 R)
  (W : left-module-Commutative-Ring l3 R)
  (f : linear-map-left-module-Commutative-Ring R V W)
  where

  abstract
    is-zero-map-zero-linear-map-left-module-Commutative-Ring :
      is-zero-left-module-Commutative-Ring R W
        ( map-linear-map-left-module-Commutative-Ring R V W f
          ( zero-left-module-Commutative-Ring R V))
    is-zero-map-zero-linear-map-left-module-Commutative-Ring =
      is-zero-map-zero-linear-map-left-module-Ring
        ( ring-Commutative-Ring R)
        ( V)
        ( W)
        ( f)
```

### A linear map maps `-v` to the negation of the map of `v`

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (V : left-module-Commutative-Ring l2 R)
  (W : left-module-Commutative-Ring l3 R)
  (f : linear-map-left-module-Commutative-Ring R V W)
  where

  abstract
    map-neg-linear-map-left-module-Commutative-Ring :
      (v : type-left-module-Commutative-Ring R V) →
      map-linear-map-left-module-Commutative-Ring R V W f
        ( neg-left-module-Commutative-Ring R V v) ＝
      neg-left-module-Commutative-Ring R W
        ( map-linear-map-left-module-Commutative-Ring R V W f v)
    map-neg-linear-map-left-module-Commutative-Ring =
      map-neg-linear-map-left-module-Ring
        ( ring-Commutative-Ring R)
        ( V)
        ( W)
        ( f)
```

### The composition of linear maps is linear

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Commutative-Ring l1)
  (V : left-module-Commutative-Ring l2 R)
  (W : left-module-Commutative-Ring l3 R)
  (X : left-module-Commutative-Ring l4 R)
  (g :
    type-left-module-Commutative-Ring R W →
    type-left-module-Commutative-Ring R X)
  (f :
    type-left-module-Commutative-Ring R V →
    type-left-module-Commutative-Ring R W)
  where

  abstract
    is-linear-comp-is-linear-map-left-module-Commutative-Ring :
      is-linear-map-left-module-Commutative-Ring R W X g →
      is-linear-map-left-module-Commutative-Ring R V W f →
      is-linear-map-left-module-Commutative-Ring R V X (g ∘ f)
    is-linear-comp-is-linear-map-left-module-Commutative-Ring =
      is-linear-comp-is-linear-map-left-module-Ring
        ( ring-Commutative-Ring R)
        ( V)
        ( W)
        ( X)
        ( g)
        ( f)
```

### The linear composition of linear maps between vector spaces

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Commutative-Ring l1)
  (V : left-module-Commutative-Ring l2 R)
  (W : left-module-Commutative-Ring l3 R)
  (X : left-module-Commutative-Ring l4 R)
  (g : linear-map-left-module-Commutative-Ring R W X)
  (f : linear-map-left-module-Commutative-Ring R V W)
  where

  comp-linear-map-left-module-Commutative-Ring :
    linear-map-left-module-Commutative-Ring R V X
  comp-linear-map-left-module-Commutative-Ring =
    comp-linear-map-left-module-Ring
      ( ring-Commutative-Ring R)
      ( V)
      ( W)
      ( X)
      ( g)
      ( f)
```

## See also

- [Linear maps between left modules over rings](linear-algebra.linear-maps-left-modules-rings.md)
- [Linear maps between vector spaces](linear-algebra.linear-maps-vector-spaces.md)
- [Scalar multiplication of linear maps between left modules over commutative rings](linear-algebra.scalar-multiplication-linear-maps-left-modules-commutative-rings.md)
