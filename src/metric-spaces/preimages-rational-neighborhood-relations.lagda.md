# Preimages of rational neighborhood relations along maps

```agda
module metric-spaces.preimages-rational-neighborhood-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.universe-levels

open import metric-spaces.monotonic-rational-neighborhoods
open import metric-spaces.rational-neighborhoods
open import metric-spaces.reflexive-rational-neighborhoods
open import metric-spaces.symmetric-rational-neighborhoods
open import metric-spaces.triangular-rational-neighborhoods
```

</details>

## Idea

Given a
[rational neighborhood relation](metric-spaces.rational-neighborhoods.md) `U` on
a type `B` and map `f : A → B`, then we may define a rational neighborhood
relation `f⁻¹U` on `A` where `x y : A` are `d`-neighbors in `f⁻¹U` if `f x` and
`f y` are `d`-neighbors in `U`. This is the
{{#concept "preimage" Disambiguation="rational neighborhood relation" Agda=preimage-Rational-Neighborhood-Relation}}
of `U` along `f`.

## Definitions

### The induced rational neighborhood relation on the preimage of a map

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Rational-Neighborhood-Relation l2 B)
  where

  preimage-Rational-Neighborhood-Relation : Rational-Neighborhood-Relation l2 A
  preimage-Rational-Neighborhood-Relation d x y = V d (f x) (f y)
```

## Properties

### The preimage of a reflexive rational neighborhood relation is reflexive

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Rational-Neighborhood-Relation l2 B)
  (R : is-reflexive-Rational-Neighborhood-Relation V)
  where

  preserves-reflexive-preimage-Rational-Neighborhood-Relation :
    is-reflexive-Rational-Neighborhood-Relation
      (preimage-Rational-Neighborhood-Relation f V)
  preserves-reflexive-preimage-Rational-Neighborhood-Relation d x = R d (f x)
```

### The preimage of a symmetric rational neighborhood relation is symmetric

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Rational-Neighborhood-Relation l2 B)
  (S : is-symmetric-Rational-Neighborhood-Relation V)
  where

  preserves-symmetric-preimage-Rational-Neighborhood-Relation :
    is-symmetric-Rational-Neighborhood-Relation
      (preimage-Rational-Neighborhood-Relation f V)
  preserves-symmetric-preimage-Rational-Neighborhood-Relation d x y =
    S d (f x) (f y)
```

### The preimage of a monotonic rational neighborhood relation is monotonic

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Rational-Neighborhood-Relation l2 B)
  (I : is-monotonic-Rational-Neighborhood-Relation V)
  where

  preserves-monotonic-preimage-Rational-Neighborhood-Relation :
    is-monotonic-Rational-Neighborhood-Relation
      (preimage-Rational-Neighborhood-Relation f V)
  preserves-monotonic-preimage-Rational-Neighborhood-Relation x y =
    I (f x) (f y)
```

### The preimage of a triangular rational neighborhood relation is triangular

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Rational-Neighborhood-Relation l2 B)
  (T : is-triangular-Rational-Neighborhood-Relation V)
  where

  preserves-triangular-preimage-Rational-Neighborhood-Relation :
    is-triangular-Rational-Neighborhood-Relation
      (preimage-Rational-Neighborhood-Relation f V)
  preserves-triangular-preimage-Rational-Neighborhood-Relation x y z =
    T (f x) (f y) (f z)
```

### The preimage along the identity is the identity

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U : Rational-Neighborhood-Relation l2 A)
  where

  eq-preimage-id-Rational-Neighborhood-Relation :
    preimage-Rational-Neighborhood-Relation id U ＝ U
  eq-preimage-id-Rational-Neighborhood-Relation = refl
```

### The preimage of rational neighborhood relations is contravariant

```agda
module _
  {la lb lc l : Level} {A : UU la} {B : UU lb} {C : UU lc}
  (g : B → C) (f : A → B) (W : Rational-Neighborhood-Relation l C)
  where

  eq-preimage-comp-Rational-Neighborhood-Relation :
    ( preimage-Rational-Neighborhood-Relation f
      (preimage-Rational-Neighborhood-Relation g W)) ＝
    ( preimage-Rational-Neighborhood-Relation (g ∘ f) W)
  eq-preimage-comp-Rational-Neighborhood-Relation = refl
```
