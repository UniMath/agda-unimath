# Products of families of globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.products-families-of-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

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

  globular-structure-0-cell-indexed-product-Globular-Type :
    {l2 l3 : Level} (G : I → Globular-Type l2 l3) →
    globular-structure (l1 ⊔ l3) (0-cell-indexed-product-Globular-Type G)
  1-cell-globular-structure
    ( globular-structure-0-cell-indexed-product-Globular-Type G) =
    1-cell-indexed-product-Globular-Type G
  globular-structure-1-cell-globular-structure
    ( globular-structure-0-cell-indexed-product-Globular-Type G) x y =
    globular-structure-0-cell-indexed-product-Globular-Type
      ( λ i → 1-cell-globular-type-Globular-Type (G i) (x i) (y i))

  indexed-product-Globular-Type :
    {l2 l3 : Level} (G : I → Globular-Type l2 l3) →
    Globular-Type (l1 ⊔ l2) (l1 ⊔ l3)
  pr1 (indexed-product-Globular-Type G) =
    0-cell-indexed-product-Globular-Type G
  pr2 (indexed-product-Globular-Type G) =
    globular-structure-0-cell-indexed-product-Globular-Type G
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

  globular-structure-0-cell-double-indexed-product-Globular-Type :
    globular-structure
      ( l1 ⊔ l2 ⊔ l4)
      ( 0-cell-double-indexed-product-Globular-Type)
  globular-structure-0-cell-double-indexed-product-Globular-Type =
    globular-structure-0-cell-indexed-product-Globular-Type
      ( λ i → indexed-product-Globular-Type (G i))

  double-indexed-product-Globular-Type :
    Globular-Type (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l4)
  double-indexed-product-Globular-Type =
    indexed-product-Globular-Type
      ( λ i → indexed-product-Globular-Type (G i))
```
