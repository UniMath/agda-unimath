# Products of families of globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.products-families-of-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.globular-types
```

</details>

## Idea

Consider a family `G : I → Globular-Type` of [globular types](structured-types.globular-types.md) indexed by a type `I`. The {{#concept "indexed product" Disambiguation="family of globular types" Agda=indexed-product-Globular-Type}} `Π_I G` is the globular type given by

```text
  (Π_I G)₀ := (i : I) → (G i)₀
  (Π_I G)' x y := Π_I (λ i → (G i)' (x i) (y i)).
```

## Definitions

### Indexed products of globular types

```agda
module _
  {l1 : Level} {I : UU l1}
  where

  0-cell-indexed-product-Globular-Type :
    {l2 l3 : Level} (G : I → Globular-Type l2 l3) → UU (l1 ⊔ l2)
  0-cell-indexed-product-Globular-Type G =
    (i : I) → 0-cell-Globular-Type (G i)

  1-cell-indexed-product-Globular-Type :
    {l2 l3 : Level} (G : I → Globular-Type l2 l3)
    (x y : 0-cell-indexed-product-Globular-Type G) → UU (l1 ⊔ l3)
  1-cell-indexed-product-Globular-Type G x y =
    (i : I) → 1-cell-Globular-Type (G i) (x i) (y i)

  indexed-product-Globular-Type :
    {l2 l3 : Level} (G : I → Globular-Type l2 l3) →
    Globular-Type (l1 ⊔ l2) (l1 ⊔ l3)
  0-cell-Globular-Type (indexed-product-Globular-Type G) =
    0-cell-indexed-product-Globular-Type G
  1-cell-globular-type-Globular-Type (indexed-product-Globular-Type G) x y =
    indexed-product-Globular-Type
      ( λ i → 1-cell-globular-type-Globular-Type (G i) (x i) (y i))
```

### Double indexed products of families of globular types

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {J : I → UU l2}
  (G : (i : I) (j : J i) → Globular-Type l3 l4)
  where

  0-cell-double-indexed-product-Globular-Type : UU (l1 ⊔ l2 ⊔ l3)
  0-cell-double-indexed-product-Globular-Type =
    0-cell-indexed-product-Globular-Type
      ( λ i → indexed-product-Globular-Type (G i))

  1-cell-double-indexed-product-Globular-Type :
    (x y : 0-cell-double-indexed-product-Globular-Type) → UU (l1 ⊔ l2 ⊔ l4)
  1-cell-double-indexed-product-Globular-Type =
    1-cell-indexed-product-Globular-Type
      ( λ i → indexed-product-Globular-Type (G i))

  double-indexed-product-Globular-Type :
    Globular-Type (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l4)
  double-indexed-product-Globular-Type =
    indexed-product-Globular-Type
      ( λ i → indexed-product-Globular-Type (G i))
```

### Evaluating globular maps into exponents of globular types

```agda
ev-hom-indexed-product-Globular-Type :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {G : Globular-Type l2 l3} {H : I → Globular-Type l4 l5}
  (f : globular-map G (indexed-product-Globular-Type H)) →
  (i : I) → globular-map G (H i)
0-cell-globular-map (ev-hom-indexed-product-Globular-Type f i) x =
  0-cell-globular-map f x i
1-cell-globular-map-globular-map
  ( ev-hom-indexed-product-Globular-Type f i) =
  ev-hom-indexed-product-Globular-Type (1-cell-globular-map-globular-map f) i
```

### Binding families of globular maps

```agda
bind-indexed-family-globular-maps :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {G : Globular-Type l2 l3} {H : I → Globular-Type l4 l5}
  (f : (i : I) → globular-map G (H i)) →
  globular-map G (indexed-product-Globular-Type H)
0-cell-globular-map (bind-indexed-family-globular-maps f) x i =
  0-cell-globular-map (f i) x
1-cell-globular-map-globular-map (bind-indexed-family-globular-maps f) =
  bind-indexed-family-globular-maps
    ( λ i → 1-cell-globular-map-globular-map (f i))
```
