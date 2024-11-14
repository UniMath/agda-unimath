# Equivalences between globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.globular-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.globular-types
```

</details>

## Idea

A {{#concept "globular equivalence" Agda=globular-equiv}} `e` between
[globular types](structured-types.globular-types.md) `A` and `B` consists of an
[equivalence](foundation-core.equivalences.md) `e₀` of $0$-cells, and for every
pair of $n$-cells `x` and `y`, an equivalence of $(n+1)$-cells

```text
  eₙ₊₁ : (𝑛+1)-Cell A x y ≃ (𝑛+1)-Cell B (eₙ x) (eₙ y).
```

## Definitions

### Equivalences between globular types

```agda
record
  globular-equiv
    {l1 l2 l3 l4 : Level} (A : Globular-Type l1 l2) (B : Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive

  field
    0-cell-equiv-globular-equiv :
      0-cell-Globular-Type A ≃ 0-cell-Globular-Type B

  0-cell-globular-equiv : 0-cell-Globular-Type A → 0-cell-Globular-Type B
  0-cell-globular-equiv = map-equiv 0-cell-equiv-globular-equiv

  field
    1-cell-globular-equiv-globular-equiv :
      {x y : 0-cell-Globular-Type A} →
      globular-equiv
        ( 1-cell-globular-type-Globular-Type A x y)
        ( 1-cell-globular-type-Globular-Type B
          ( 0-cell-globular-equiv x)
          ( 0-cell-globular-equiv y))

open globular-equiv public

globular-map-globular-equiv :
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4} →
  globular-equiv A B → globular-map A B
0-cell-globular-map (globular-map-globular-equiv e) =
  map-equiv (0-cell-equiv-globular-equiv e)
1-cell-globular-map-globular-map (globular-map-globular-equiv e) =
  globular-map-globular-equiv (1-cell-globular-equiv-globular-equiv e)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (e : globular-equiv A B)
  where

  1-cell-equiv-globular-equiv :
    {x y : 0-cell-Globular-Type A} →
    1-cell-Globular-Type A x y ≃
    1-cell-Globular-Type B
      ( 0-cell-globular-equiv e x)
      ( 0-cell-globular-equiv e y)
  1-cell-equiv-globular-equiv =
    0-cell-equiv-globular-equiv
      ( 1-cell-globular-equiv-globular-equiv e)

  1-cell-globular-equiv :
    {x y : 0-cell-Globular-Type A} →
    1-cell-Globular-Type A x y →
    1-cell-Globular-Type B
      ( 0-cell-globular-equiv e x)
      ( 0-cell-globular-equiv e y)
  1-cell-globular-equiv =
    0-cell-globular-equiv (1-cell-globular-equiv-globular-equiv e)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (e : globular-equiv A B)
  where

  2-cell-equiv-globular-equiv :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    2-cell-Globular-Type A f g ≃
    2-cell-Globular-Type B
      ( 1-cell-globular-equiv e f)
      ( 1-cell-globular-equiv e g)
  2-cell-equiv-globular-equiv =
    1-cell-equiv-globular-equiv
      ( 1-cell-globular-equiv-globular-equiv e)

  2-cell-globular-equiv :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    2-cell-Globular-Type A f g →
    2-cell-Globular-Type B
      ( 1-cell-globular-equiv e f)
      ( 1-cell-globular-equiv e g)
  2-cell-globular-equiv =
    1-cell-globular-equiv (1-cell-globular-equiv-globular-equiv e)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (e : globular-equiv A B)
  where

  3-cell-equiv-globular-equiv :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    {H K : 2-cell-Globular-Type A f g} →
    3-cell-Globular-Type A H K ≃
    3-cell-Globular-Type B
      ( 2-cell-globular-equiv e H)
      ( 2-cell-globular-equiv e K)
  3-cell-equiv-globular-equiv =
    2-cell-equiv-globular-equiv
      ( 1-cell-globular-equiv-globular-equiv e)
```

### The identity equivalence on a globular type

```agda
id-globular-equiv :
  {l1 l2 : Level} (A : Globular-Type l1 l2) → globular-equiv A A
id-globular-equiv A =
  λ where
  .0-cell-equiv-globular-equiv → id-equiv
  .1-cell-globular-equiv-globular-equiv {x} {y} →
    id-globular-equiv (1-cell-globular-type-Globular-Type A x y)
```

### Composition of equivalences of globular types

```agda
comp-globular-equiv :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Globular-Type l1 l2}
  {B : Globular-Type l3 l4}
  {C : Globular-Type l5 l6} →
  globular-equiv B C → globular-equiv A B → globular-equiv A C
comp-globular-equiv g f =
  λ where
  .0-cell-equiv-globular-equiv →
    0-cell-equiv-globular-equiv g ∘e 0-cell-equiv-globular-equiv f
  .1-cell-globular-equiv-globular-equiv →
    comp-globular-equiv
      ( 1-cell-globular-equiv-globular-equiv g)
      ( 1-cell-globular-equiv-globular-equiv f)
```
