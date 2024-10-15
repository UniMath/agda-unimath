# Dependent coproducts of globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.dependent-coproducts-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.dependent-globular-types
open import structured-types.globular-maps
open import structured-types.globular-types
```

</details>

## Idea

Consider a [dependent globular type](structured-types.dependent-globular-types.md) `H` over a [globular type](structured-types.globular-types.md) `G`. The {{#concept "dependent coproduct" Disambiguation="globular types" Agda=Σ-Globular-Type}} `Σ G H` of `H` is the globular type given by

```text
  (Σ G H)₀ := Σ G₀ H₀
  (Σ G H)' (x , y) (x' , y') := Σ (G' x x') (H' y y').
```

## Definitions

### Dependent coproducts of dependent globular types

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

  1-cell-Σ-Globular-Type :
    (x y : 0-cell-Globular-Type (Σ-Globular-Type H)) → UU (l2 ⊔ l4)
  1-cell-Σ-Globular-Type =
    1-cell-Globular-Type (Σ-Globular-Type H)

  2-cell-Σ-Globular-Type :
    {x y : 0-cell-Σ-Globular-Type} →
    (f g : 1-cell-Σ-Globular-Type x y) → UU (l2 ⊔ l4)
  2-cell-Σ-Globular-Type =
    2-cell-Globular-Type (Σ-Globular-Type H)
```

### The first projection out of the dependent coproduct of a dependent globular type

```agda
pr1-Σ-Globular-Type :
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
  (H : Dependent-Globular-Type l3 l4 G) →
  globular-map (Σ-Globular-Type H) G
0-cell-globular-map (pr1-Σ-Globular-Type H) = pr1
1-cell-globular-map-globular-map (pr1-Σ-Globular-Type H) =
  pr1-Σ-Globular-Type
    ( 1-cell-dependent-globular-type-Dependent-Globular-Type H _ _)
```
