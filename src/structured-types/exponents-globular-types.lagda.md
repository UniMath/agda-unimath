# Exponents of globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.exponents-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.globular-types
open import structured-types.products-families-of-globular-types
```

</details>

## Idea

Consider a family `G : I → Globular-Type` of [globular types](structured-types.globular-types.md) indexed by a type `I`. We construct a globular type `Π_I G`.

## Definitions

### Exponents of globular types

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (G : Globular-Type l2 l3)
  where

  0-cell-exponent-Globular-Type : UU (l1 ⊔ l2)
  0-cell-exponent-Globular-Type =
    0-cell-indexed-product-Globular-Type (λ (x : A) → G)

  1-cell-exponent-Globular-Type :
    (x y : 0-cell-exponent-Globular-Type) → UU (l1 ⊔ l3)
  1-cell-exponent-Globular-Type =
    1-cell-indexed-product-Globular-Type (λ (x : A) → G)

  exponent-Globular-Type : Globular-Type (l1 ⊔ l2) (l1 ⊔ l3)
  exponent-Globular-Type = indexed-product-Globular-Type (λ (x : A) → G)
```

### Double exponentials of globular types

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : UU l2) (G : Globular-Type l3 l4)
  where

  0-cell-double-exponent-Globular-Type : UU (l1 ⊔ l2 ⊔ l3)
  0-cell-double-exponent-Globular-Type =
    0-cell-double-indexed-product-Globular-Type (λ (x : A) (y : B) → G)

  1-cell-double-exponent-Globular-Type :
    (x y : 0-cell-double-exponent-Globular-Type) → UU (l1 ⊔ l2 ⊔ l4)
  1-cell-double-exponent-Globular-Type =
    1-cell-double-indexed-product-Globular-Type (λ (x : A) (y : B) → G)

  double-exponent-Globular-Type : Globular-Type (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l4)
  double-exponent-Globular-Type =
    double-indexed-product-Globular-Type (λ (x : A) (y : B) → G)  
```

### Evaluating globular maps into exponents of globular types

```agda
ev-hom-exponent-Globular-Type :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {G : Globular-Type l2 l3} {H : Globular-Type l4 l5}
  (f : globular-map G (exponent-Globular-Type I H)) →
  I → globular-map G H
ev-hom-exponent-Globular-Type = ev-hom-indexed-product-Globular-Type
```

### Binding families of globular maps

```agda
bind-family-globular-maps :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {G : Globular-Type l2 l3} {H : Globular-Type l4 l5}
  (f : I → globular-map G H) → globular-map G (exponent-Globular-Type I H)
bind-family-globular-maps = bind-indexed-family-globular-maps
```
