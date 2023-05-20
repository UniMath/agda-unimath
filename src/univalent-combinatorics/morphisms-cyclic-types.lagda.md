# Morphisms of cyclic types

```agda
module univalent-combinatorics.morphisms-cyclic-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.universe-levels

open import univalent-combinatorics.cyclic-types
```

</details>

## Idea

A **morphism of [cyclic types](univalent-combinatorics.cyclic-types.md)** from a cyclic type `(X,f)` of order `n` to a cyclic type `(Y,g)` of order `m` consists of a map `h : X → Y` and a map `d : X → ℕ` where the value `d x : ℕ` is the number of times `h` winds around the cyclic type `(Y,g)` before stepping from the value `h x` to the value `h (f x)`.

## Definitions

### Morphisms of cyclic types

```agda
module _
  {l1 l2 : Level} (m n : ℕ) (X : Cyclic-Type l1 m) (Y : Cyclic-Type l2 n)
  where

  hom-Cyclic-Type : UU (l1 ⊔ l2)
  hom-Cyclic-Type =
    ( type-Cyclic-Type m X → type-Cyclic-Type n Y) ×
    ( type-Cyclic-Type m X → ℕ)

  module _
    (f : hom-Cyclic-Type)
    where

    map-hom-Cyclic-Type : type-Cyclic-Type m X → type-Cyclic-Type n Y
    map-hom-Cyclic-Type = pr1 f

    degree-at-value-hom-Cyclic-Type : type-Cyclic-Type m X → ℕ
    degree-at-value-hom-Cyclic-Type = pr2 f
```

### Identity morphisms of cyclic types

```agda
module _
  {l1 : Level} (m : ℕ) (X : Cyclic-Type l1 m)
  where

  id-hom-Cyclic-Type : hom-Cyclic-Type m m X X
  pr1 id-hom-Cyclic-Type = id
  pr2 id-hom-Cyclic-Type x = 0
```

### Composition of morphisms of cyclic types

```agda
module _
  {l1 l2 l3 : Level} (l m n : ℕ)
  (X : Cyclic-Type l1 l)
  (Y : Cyclic-Type l2 m)
  (Z : Cyclic-Type l3 n)
  where

  comp-hom-Cyclic-Type :
    hom-Cyclic-Type m n Y Z → hom-Cyclic-Type l m X Y → hom-Cyclic-Type l n X Z
  pr1 (comp-hom-Cyclic-Type g f) =
    map-hom-Cyclic-Type m n Y Z g ∘ map-hom-Cyclic-Type l m X Y f
  pr2 (comp-hom-Cyclic-Type g f) = {!!}
```
