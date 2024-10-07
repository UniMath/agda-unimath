# Equivalences between globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.equivalences-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguation="globular types" Agda=equiv-Globular-Type}}
`f` between [globular types](structured-types.globular-types.md) `A` and `B` is
an equivalence `F₀` of $0$-cells, and for every pair of $n$-cells `x` and `y`,
an equivalence of $(n+1)$-cells

```text
  Fₙ₊₁ : (𝑛+1)-Cell A x y ≃ (𝑛+1)-Cell B (Fₙ x) (Fₙ y).
```

## Definitions

### Equivalences between globular types

```agda
record
  equiv-Globular-Type
  {l1 l2 l3 l4 : Level} (A : Globular-Type l1 l2) (B : Globular-Type l3 l4)
  : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    0-cell-equiv-Globular-Type :
      0-cell-Globular-Type A ≃ 0-cell-Globular-Type B

  map-0-cell-equiv-Globular-Type :
      0-cell-Globular-Type A → 0-cell-Globular-Type B
  map-0-cell-equiv-Globular-Type = pr1 0-cell-equiv-Globular-Type

  field
    globular-type-1-cell-equiv-Globular-Type :
      {x y : 0-cell-Globular-Type A} →
      equiv-Globular-Type
        ( 1-cell-globular-type-Globular-Type A x y)
        ( 1-cell-globular-type-Globular-Type B
          ( map-0-cell-equiv-Globular-Type x)
          ( map-0-cell-equiv-Globular-Type y))

open equiv-Globular-Type public

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (F : equiv-Globular-Type A B)
  where

  1-cell-equiv-Globular-Type :
    {x y : 0-cell-Globular-Type A} →
    1-cell-Globular-Type A x y ≃
    1-cell-Globular-Type B
      ( map-0-cell-equiv-Globular-Type F x)
      ( map-0-cell-equiv-Globular-Type F y)
  1-cell-equiv-Globular-Type =
    0-cell-equiv-Globular-Type (globular-type-1-cell-equiv-Globular-Type F)

  map-1-cell-equiv-Globular-Type :
    {x y : 0-cell-Globular-Type A} →
    1-cell-Globular-Type A x y →
    1-cell-Globular-Type B
      ( map-0-cell-equiv-Globular-Type F x)
      ( map-0-cell-equiv-Globular-Type F y)
  map-1-cell-equiv-Globular-Type =
    map-0-cell-equiv-Globular-Type (globular-type-1-cell-equiv-Globular-Type F)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (F : equiv-Globular-Type A B)
  where

  2-cell-equiv-Globular-Type :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    2-cell-Globular-Type A f g ≃
    2-cell-Globular-Type B
      ( map-1-cell-equiv-Globular-Type F f)
      ( map-1-cell-equiv-Globular-Type F g)
  2-cell-equiv-Globular-Type =
    1-cell-equiv-Globular-Type (globular-type-1-cell-equiv-Globular-Type F)

  map-2-cell-equiv-Globular-Type :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    2-cell-Globular-Type A f g →
    2-cell-Globular-Type B
      ( map-1-cell-equiv-Globular-Type F f)
      ( map-1-cell-equiv-Globular-Type F g)
  map-2-cell-equiv-Globular-Type =
    map-1-cell-equiv-Globular-Type (globular-type-1-cell-equiv-Globular-Type F)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (F : equiv-Globular-Type A B)
  where

  3-cell-equiv-Globular-Type :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    {H K : 2-cell-Globular-Type A f g} →
    3-cell-Globular-Type A H K ≃
    3-cell-Globular-Type B
      ( map-2-cell-equiv-Globular-Type F H)
      ( map-2-cell-equiv-Globular-Type F K)
  3-cell-equiv-Globular-Type =
    2-cell-equiv-Globular-Type (globular-type-1-cell-equiv-Globular-Type F)
```

### The identity equiv on a globular type

```agda
id-equiv-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2) → equiv-Globular-Type A A
id-equiv-Globular-Type A =
  λ where
  .0-cell-equiv-Globular-Type → id-equiv
  .globular-type-1-cell-equiv-Globular-Type {x} {y} →
    id-equiv-Globular-Type (1-cell-globular-type-Globular-Type A x y)
```

### Composition of equivalences of globular types

```agda
comp-equiv-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Globular-Type l1 l2}
  {B : Globular-Type l3 l4}
  {C : Globular-Type l5 l6} →
  equiv-Globular-Type B C → equiv-Globular-Type A B → equiv-Globular-Type A C
comp-equiv-Globular-Type g f =
  λ where
  .0-cell-equiv-Globular-Type →
    0-cell-equiv-Globular-Type g ∘e 0-cell-equiv-Globular-Type f
  .globular-type-1-cell-equiv-Globular-Type →
    comp-equiv-Globular-Type
      ( globular-type-1-cell-equiv-Globular-Type g)
      ( globular-type-1-cell-equiv-Globular-Type f)
```
