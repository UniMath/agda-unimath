# Dependent sums of globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.dependent-sums-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.base-change-dependent-globular-types
open import structured-types.dependent-globular-types
open import structured-types.globular-maps
open import structured-types.globular-types
open import structured-types.sections-dependent-globular-types
```

</details>

## Idea

Consider a
[dependent globular type](structured-types.dependent-globular-types.md) `H` over
a [globular type](structured-types.globular-types.md) `G`. The
{{#concept "dependent sum" Disambiguation="globular types" Agda=Σ-Globular-Type}}
`Σ G H` of `H` is the globular type given by

```text
  (Σ G H)₀ := Σ G₀ H₀
  (Σ G H)' (x , y) (x' , y') := Σ (G' x x') (H' y y').
```

## Definitions

### Dependent sums of dependent globular types

```agda
Σ-Globular-Type :
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
  (H : Dependent-Globular-Type l3 l4 G) → Globular-Type (l1 ⊔ l3) (l2 ⊔ l4)
0-cell-Globular-Type (Σ-Globular-Type H) =
  Σ _ (0-cell-Dependent-Globular-Type H)
1-cell-globular-type-Globular-Type (Σ-Globular-Type H) (x , y) (x' , y') =
  Σ-Globular-Type
    ( 1-cell-dependent-globular-type-Dependent-Globular-Type H y y')

module _
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
  (H : Dependent-Globular-Type l3 l4 G)
  where

  0-cell-Σ-Globular-Type : UU (l1 ⊔ l3)
  0-cell-Σ-Globular-Type =
    0-cell-Globular-Type (Σ-Globular-Type H)

  1-cell-globular-type-Σ-Globular-Type :
    (x y : 0-cell-Σ-Globular-Type) → Globular-Type (l2 ⊔ l4) (l2 ⊔ l4)
  1-cell-globular-type-Σ-Globular-Type =
    1-cell-globular-type-Globular-Type (Σ-Globular-Type H)

  1-cell-Σ-Globular-Type :
    (x y : 0-cell-Globular-Type (Σ-Globular-Type H)) → UU (l2 ⊔ l4)
  1-cell-Σ-Globular-Type =
    1-cell-Globular-Type (Σ-Globular-Type H)

  2-cell-globular-type-Σ-Globular-Type :
    {x y : 0-cell-Σ-Globular-Type}
    (f g : 1-cell-Σ-Globular-Type x y) → Globular-Type (l2 ⊔ l4) (l2 ⊔ l4)
  2-cell-globular-type-Σ-Globular-Type =
    2-cell-globular-type-Globular-Type (Σ-Globular-Type H)

  2-cell-Σ-Globular-Type :
    {x y : 0-cell-Σ-Globular-Type} →
    (f g : 1-cell-Σ-Globular-Type x y) → UU (l2 ⊔ l4)
  2-cell-Σ-Globular-Type =
    2-cell-Globular-Type (Σ-Globular-Type H)
```

### The first projection out of the dependent sum of a dependent globular type

```agda
pr1-Σ-Globular-Type :
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
  (H : Dependent-Globular-Type l3 l4 G) →
  globular-map (Σ-Globular-Type H) G
0-cell-globular-map (pr1-Σ-Globular-Type H) = pr1
1-cell-globular-map-globular-map (pr1-Σ-Globular-Type H) =
  pr1-Σ-Globular-Type
    ( 1-cell-dependent-globular-type-Dependent-Globular-Type H _ _)

module _
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
  (H : Dependent-Globular-Type l3 l4 G)
  where

  0-cell-pr1-Σ-Globular-Type :
    0-cell-Σ-Globular-Type H → 0-cell-Globular-Type G
  0-cell-pr1-Σ-Globular-Type =
    0-cell-globular-map (pr1-Σ-Globular-Type H)

  1-cell-globular-map-pr1-Σ-Globular-Type :
    (x y : 0-cell-Σ-Globular-Type H) →
    globular-map
      ( 1-cell-globular-type-Σ-Globular-Type H x y)
      ( 1-cell-globular-type-Globular-Type G
        ( 0-cell-pr1-Σ-Globular-Type x)
        ( 0-cell-pr1-Σ-Globular-Type y))
  1-cell-globular-map-pr1-Σ-Globular-Type x y =
    1-cell-globular-map-globular-map (pr1-Σ-Globular-Type H)

  1-cell-pr1-Σ-Globular-Type :
    {x y : 0-cell-Σ-Globular-Type H} →
    1-cell-Σ-Globular-Type H x y →
    1-cell-Globular-Type G
      ( 0-cell-pr1-Σ-Globular-Type x)
      ( 0-cell-pr1-Σ-Globular-Type y)
  1-cell-pr1-Σ-Globular-Type =
    1-cell-globular-map (pr1-Σ-Globular-Type H)
```

### The second projection of a dependent sum of globular types

```agda
pr2-Σ-Globular-Type :
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
  (H : Dependent-Globular-Type l3 l4 G) →
  section-Dependent-Globular-Type
    ( base-change-Dependent-Globular-Type (pr1-Σ-Globular-Type H) H)
0-cell-section-Dependent-Globular-Type (pr2-Σ-Globular-Type H) = pr2
1-cell-section-section-Dependent-Globular-Type (pr2-Σ-Globular-Type H) =
  pr2-Σ-Globular-Type
    ( 1-cell-dependent-globular-type-Dependent-Globular-Type H _ _)

module _
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
  (H : Dependent-Globular-Type l3 l4 G)
  where

  0-cell-pr2-Σ-Globular-Type :
    (x : 0-cell-Σ-Globular-Type H) →
    0-cell-base-change-Dependent-Globular-Type (pr1-Σ-Globular-Type H) H x
  0-cell-pr2-Σ-Globular-Type =
    0-cell-section-Dependent-Globular-Type (pr2-Σ-Globular-Type H)

  1-cell-section-pr2-Σ-Globular-Type :
    {x x' : 0-cell-Σ-Globular-Type H} →
    section-Dependent-Globular-Type
      ( 1-cell-dependent-globular-type-base-change-Dependent-Globular-Type
        ( pr1-Σ-Globular-Type H)
        ( H)
        ( 0-cell-pr2-Σ-Globular-Type x)
        ( 0-cell-pr2-Σ-Globular-Type x'))
  1-cell-section-pr2-Σ-Globular-Type =
    1-cell-section-section-Dependent-Globular-Type (pr2-Σ-Globular-Type H)

  1-cell-pr2-Σ-Globular-Type :
    {x x' : 0-cell-Σ-Globular-Type H}
    (f : 1-cell-Σ-Globular-Type H x x') →
    1-cell-base-change-Dependent-Globular-Type
      ( pr1-Σ-Globular-Type H)
      ( H)
      ( 0-cell-pr2-Σ-Globular-Type x)
      ( 0-cell-pr2-Σ-Globular-Type x')
      ( f)
  1-cell-pr2-Σ-Globular-Type =
    1-cell-section-Dependent-Globular-Type
      ( base-change-Dependent-Globular-Type (pr1-Σ-Globular-Type H) H)
      ( pr2-Σ-Globular-Type H)
```
