# Nets in metric spaces

```agda
module metric-spaces.nets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.images
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.approximations-metric-spaces
open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.images-isometries-metric-spaces
open import metric-spaces.images-metric-spaces
open import metric-spaces.images-short-functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-uniformly-continuous-functions-metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
open import univalent-combinatorics.inhabited-finitely-enumerable-subtypes
```

</details>

## Idea

For an `ε : ℚ⁺`, an `ε`-{{#concept "net" disambiguation="in a metric space"}} to
a [metric space](metric-spaces.metric-spaces.md) `X` is a
[finitely enumerable](univalent-combinatorics.finitely-enumerable-subtypes.md)
ε-[approximation](metric-spaces.approximations-metric-spaces.md) of `X`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (ε : ℚ⁺)
  (S : finitely-enumerable-subtype l3 (type-Metric-Space X))
  where

  is-net-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-net-prop-Metric-Space =
    is-approximation-prop-Metric-Space X ε
      ( subtype-finitely-enumerable-subtype S)

  is-net-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-net-Metric-Space = type-Prop is-net-prop-Metric-Space

net-Metric-Space :
  {l1 l2 : Level} (l3 : Level) → Metric-Space l1 l2 → ℚ⁺ →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
net-Metric-Space l3 X ε =
  type-subtype (is-net-prop-Metric-Space {l3 = l3} X ε)

module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (ε : ℚ⁺)
  (N : net-Metric-Space l3 X ε)
  where

  finitely-enumerable-subset-net-Metric-Space :
    finitely-enumerable-subtype l3 (type-Metric-Space X)
  finitely-enumerable-subset-net-Metric-Space = pr1 N

  subset-net-Metric-Space : subset-Metric-Space l3 X
  subset-net-Metric-Space =
    subtype-finitely-enumerable-subtype
      ( finitely-enumerable-subset-net-Metric-Space)

  is-approximation-subset-net-Metric-Space :
    is-approximation-Metric-Space X ε subset-net-Metric-Space
  is-approximation-subset-net-Metric-Space = pr2 N

  approximation-net-Metric-Space : approximation-Metric-Space l3 X ε
  approximation-net-Metric-Space =
    ( subset-net-Metric-Space ,
      is-approximation-subset-net-Metric-Space)
```

### If a metric space is inhabited, so is any net on it

```agda
module _
  {l1 l2 l3 : Level}
  (X : Metric-Space l1 l2) (|X| : is-inhabited (type-Metric-Space X))
  (ε : ℚ⁺) (S : net-Metric-Space l3 X ε)
  where

  abstract
    is-inhabited-net-inhabited-Metric-Space :
      is-inhabited-finitely-enumerable-subtype (pr1 S)
    is-inhabited-net-inhabited-Metric-Space =
      is-inhabited-is-approximation-inhabited-Metric-Space X |X| ε
        ( subset-net-Metric-Space X ε S)
        ( is-approximation-subset-net-Metric-Space X ε S)

  inhabited-finitely-enumerable-subtype-net-Metric-Space :
    inhabited-finitely-enumerable-subtype l3 (type-Metric-Space X)
  inhabited-finitely-enumerable-subtype-net-Metric-Space =
    ( finitely-enumerable-subset-net-Metric-Space X ε S ,
      is-inhabited-net-inhabited-Metric-Space)
```

## Properties

### If `μ` is a modulus of uniform continuity for `f : X → Y` and `N` is a `(μ ε)`-net of `X`, then `im f N` is an `ε`-net of `im f X`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y) {μ : ℚ⁺ → ℚ⁺}
  (is-modulus-ucont-f-μ :
    is-modulus-of-uniform-continuity-function-Metric-Space X Y f μ)
  (ε : ℚ⁺) (N : net-Metric-Space l5 X (μ ε))
  where

  net-im-uniformly-continuous-function-net-Metric-Space :
    net-Metric-Space (l1 ⊔ l3 ⊔ l5) (im-Metric-Space X Y f) ε
  net-im-uniformly-continuous-function-net-Metric-Space =
    ( im-finitely-enumerable-subtype
      ( map-unit-im f)
      ( finitely-enumerable-subset-net-Metric-Space X (μ ε) N) ,
      is-approximation-im-uniformly-continuous-function-approximation-Metric-Space
        ( X)
        ( Y)
        ( f)
        ( is-modulus-ucont-f-μ)
        ( ε)
        ( approximation-net-Metric-Space X (μ ε) N))
```

### If `f : X → Y` is a short function and `N` is an `ε`-net of `X`, then `im f N` is an `ε`-net of `im f X`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : short-function-Metric-Space X Y)
  (ε : ℚ⁺) (N : net-Metric-Space l5 X ε)
  where

  net-im-short-function-net-Metric-Space :
    net-Metric-Space
      ( l1 ⊔ l3 ⊔ l5)
      ( im-short-function-Metric-Space X Y f)
      ( ε)
  net-im-short-function-net-Metric-Space =
    net-im-uniformly-continuous-function-net-Metric-Space
      ( X)
      ( Y)
      ( map-short-function-Metric-Space X Y f)
      ( is-modulus-of-uniform-continuity-id-is-short-function-Metric-Space
        ( X)
        ( Y)
        ( map-short-function-Metric-Space X Y f)
        ( is-short-map-short-function-Metric-Space X Y f))
      ( ε)
      ( N)
```

### If `f : X → Y` is an isometry and `N` is an `ε`-net of `X`, then `im f N` is an `ε`-net of `im f X`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : isometry-Metric-Space X Y)
  (ε : ℚ⁺) (N : net-Metric-Space l5 X ε)
  where

  net-im-isometry-net-Metric-Space :
    net-Metric-Space
      ( l1 ⊔ l3 ⊔ l5)
      ( im-isometry-Metric-Space X Y f)
      ( ε)
  net-im-isometry-net-Metric-Space =
    net-im-short-function-net-Metric-Space X Y
      ( short-isometry-Metric-Space X Y f)
      ( ε)
      ( N)
```

### If `f : X ≃ Y` is an isometric equivalence and `N` is an `ε`-net of `X`, then `im f A` is an `ε`-net of `Y`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : isometric-equiv-Metric-Space X Y)
  (ε : ℚ⁺) (N : net-Metric-Space l5 X ε)
  where

  net-im-isometric-equiv-net-Metric-Space : net-Metric-Space (l1 ⊔ l3 ⊔ l5) Y ε
  net-im-isometric-equiv-net-Metric-Space =
    ( im-finitely-enumerable-subtype
        ( map-isometric-equiv-Metric-Space X Y f)
        ( finitely-enumerable-subset-net-Metric-Space X ε N) ,
      is-approximation-im-isometric-equiv-approximation-Metric-Space X Y f ε
        ( approximation-net-Metric-Space X ε N))
```

### Cartesian products of nets of metric spaces

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (ε : ℚ⁺) (M : net-Metric-Space l5 X ε) (N : net-Metric-Space l6 Y ε)
  where

  product-net-Metric-Space :
    net-Metric-Space (l5 ⊔ l6) (product-Metric-Space X Y) ε
  product-net-Metric-Space =
    ( product-finitely-enumerable-subtype
        ( finitely-enumerable-subset-net-Metric-Space X ε M)
        ( finitely-enumerable-subset-net-Metric-Space Y ε N) ,
      is-approximation-product-approximation-Metric-Space X Y ε
        ( approximation-net-Metric-Space X ε M)
        ( approximation-net-Metric-Space Y ε N))
```
