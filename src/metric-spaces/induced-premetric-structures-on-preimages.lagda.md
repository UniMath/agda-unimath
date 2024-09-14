# Induced premetric structures on preimages

```agda
module metric-spaces.induced-premetric-structures-on-preimages where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.universe-levels

open import metric-spaces.local-premetric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

Any [premetric structure](metric-spaces.premetric-structures.md) `U` on a type
`B` and map `f : A → B` defines a premetric on `A` where `x y : A` are
`d`-neighbors in `A` if `f x` and `f y` are `d`-neighbors in `U`.

In this premetric, upper bounds of the distance between `(x y : A)` are upper
bounds of the distance between `f x` and `f y` in `U`.

This is the
{{#concept "preimage" Disambiguation="of a premetric structure" Agda=preimage-Premetric}}
of a premetric.

## Definitions

### The induced premetric on the preimage of a map

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Premetric l2 B)
  where

  preimage-Premetric : Premetric l2 A
  preimage-Premetric d x y = V d (f x) (f y)
```

## Properties

### The preimage of a reflexive premetric is reflexive

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Premetric l2 B) (R : is-reflexive-Premetric V)
  where

  preserves-reflexive-preimage-Premetric :
    is-reflexive-Premetric (preimage-Premetric f V)
  preserves-reflexive-preimage-Premetric d x = R d (f x)
```

### The preimage of a symmetric premetric is symmetric

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Premetric l2 B) (S : is-symmetric-Premetric V)
  where

  preserves-symmetric-preimage-Premetric :
    is-symmetric-Premetric (preimage-Premetric f V)
  preserves-symmetric-preimage-Premetric d x y = S d (f x) (f y)
```

### The preimage of a monotonic premetric is monotonic

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Premetric l2 B) (I : is-monotonic-Premetric V)
  where

  preserves-monotonic-preimage-Premetric :
    is-monotonic-Premetric (preimage-Premetric f V)
  preserves-monotonic-preimage-Premetric x y = I (f x) (f y)
```

### The preimage of a triangular premetric is triangular

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'} (f : A → B)
  (V : Premetric l2 B) (T : is-triangular-Premetric V)
  where

  preserves-triangular-preimage-Premetric :
    is-triangular-Premetric (preimage-Premetric f V)
  preserves-triangular-preimage-Premetric x y z = T (f x) (f y) (f z)
```

### The preimage of a tight metric along an injective map is tight

```agda
module _
  {l1 l1' l2 : Level} {A : UU l1} {B : UU l1'}
  (f : A → B) (V : Premetric l2 B)
  (I : is-injective f)
  (T : is-tight-Premetric V)
  where

  preserves-tight-injective-preimage-Premetric :
    is-tight-Premetric (preimage-Premetric f V)
  preserves-tight-injective-preimage-Premetric x y =
    I ∘ (T (f x) (f y))
```

### The preimage along the identity is the identity

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U : Premetric l2 A)
  where

  eq-preimage-id-Premetric : preimage-Premetric id U ＝ U
  eq-preimage-id-Premetric = refl
```

### The preimage of premetrics is contravariant

```agda
module _
  {la lb lc l : Level} {A : UU la} {B : UU lb} {C : UU lc}
  (g : B → C) (f : A → B) (W : Premetric l C)
  where

  eq-preimage-comp-Premetric :
    preimage-Premetric f (preimage-Premetric g W) ＝
    preimage-Premetric (g ∘ f) W
  eq-preimage-comp-Premetric = refl
```
