# The pullback of premetric structures

```agda
module metric-spaces.pullback-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.universe-levels

open import metric-spaces.premetric-structures
```

</details>

## Idea

Any [premetric structure](metric-spaces.premetric-structures.md) on a type `B`
and map `f : A → B` defines a premetric on `A` where `x y : A` are
`d`-neighbours in `A` if `f x` and `f y` are `d`-neighbours in `B`.

This is the
{{#concept "pullback" Disambiguation="premetric" Agda=pullback-Premetric}} of a
premetric.

## Definitions

### The pullback of a premetric along a map

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Premetric l2 B)
  where

  pullback-Premetric : Premetric l2 A
  pullback-Premetric d x y = V d (f x) (f y)
```

## Properties

### The pullback of a reflexive premetric is reflexive

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Premetric l2 B) (R : is-reflexive-Premetric V)
  where

  preserves-reflexive-pullback-Premetric :
    is-reflexive-Premetric (pullback-Premetric f V)
  preserves-reflexive-pullback-Premetric d x = R d (f x)
```

### The pullback of a symmetric premetric is symmetric

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Premetric l2 B) (S : is-symmetric-Premetric V)
  where

  preserves-symmetric-pullback-Premetric :
    is-symmetric-Premetric (pullback-Premetric f V)
  preserves-symmetric-pullback-Premetric d x y = S d (f x) (f y)
```

### The pullback of a monotonic premetric is monotonic

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Premetric l2 B) (I : is-monotonic-Premetric V)
  where

  preserves-monotonic-pullback-Premetric :
    is-monotonic-Premetric (pullback-Premetric f V)
  preserves-monotonic-pullback-Premetric x y = I (f x) (f y)
```

### The pullback of a triangular premetric is triangular

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Premetric l2 B) (T : is-triangular-Premetric V)
  where

  preserves-triangular-pullback-Premetric :
    is-triangular-Premetric (pullback-Premetric f V)
  preserves-triangular-pullback-Premetric x y z = T (f x) (f y) (f z)
```

### The pulback of a tight metric along an injective map is tight

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'}
  (f : A → B) (V : Premetric l2 B)
  (I : is-injective f)
  (T : is-tight-Premetric V)
  where

  preserves-tight-injective-pullback-Premetric :
    is-tight-Premetric (pullback-Premetric f V)
  preserves-tight-injective-pullback-Premetric x y =
    I ∘ (T (f x) (f y))
```

### The pullback along the identity is the identity

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U : Premetric l2 A)
  where

  eq-pullback-id-Premetric : pullback-Premetric id U ＝ U
  eq-pullback-id-Premetric = refl
```

### The pullback of premetrics is contravariant

```agda
module _
  {la lb lc l : Level} {A : UU la} {B : UU lb} {C : UU lc}
  (g : B → C) (f : A → B) (W : Premetric l C)
  where

  eq-pullback-comp-Premetric :
    pullback-Premetric f (pullback-Premetric g W) ＝
    pullback-Premetric (g ∘ f) W
  eq-pullback-comp-Premetric = refl
```
