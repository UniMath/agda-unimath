# Exponentials of globular types

```agda
{-# OPTIONS --guardedness #-}

open import foundation.function-extensionality-axiom

module
  globular-types.exponentials-globular-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.globular-maps funext
open import globular-types.globular-types
open import globular-types.products-families-of-globular-types funext
```

</details>

## Idea

Consider a family `G : I → Globular-Type` of
[globular types](globular-types.globular-types.md) indexed by a type `I`. We
construct a globular type `Π_I G`.

## Definitions

### Exponentials of globular types

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (G : Globular-Type l2 l3)
  where

  0-cell-exponential-Globular-Type : UU (l1 ⊔ l2)
  0-cell-exponential-Globular-Type =
    0-cell-indexed-product-Globular-Type (λ (x : A) → G)

  1-cell-exponential-Globular-Type :
    (x y : 0-cell-exponential-Globular-Type) → UU (l1 ⊔ l3)
  1-cell-exponential-Globular-Type =
    1-cell-indexed-product-Globular-Type (λ (x : A) → G)

  exponential-Globular-Type : Globular-Type (l1 ⊔ l2) (l1 ⊔ l3)
  exponential-Globular-Type = indexed-product-Globular-Type (λ (x : A) → G)
```

### Double exponentials of globular types

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : UU l2) (G : Globular-Type l3 l4)
  where

  0-cell-double-exponential-Globular-Type : UU (l1 ⊔ l2 ⊔ l3)
  0-cell-double-exponential-Globular-Type =
    0-cell-double-indexed-product-Globular-Type (λ (x : A) (y : B) → G)

  1-cell-double-exponential-Globular-Type :
    (x y : 0-cell-double-exponential-Globular-Type) → UU (l1 ⊔ l2 ⊔ l4)
  1-cell-double-exponential-Globular-Type =
    1-cell-double-indexed-product-Globular-Type (λ (x : A) (y : B) → G)

  double-exponential-Globular-Type : Globular-Type (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l4)
  double-exponential-Globular-Type =
    double-indexed-product-Globular-Type (λ (x : A) (y : B) → G)
```

### Evaluating globular maps into exponentials of globular types

```agda
ev-hom-exponential-Globular-Type :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {G : Globular-Type l2 l3} {H : Globular-Type l4 l5}
  (f : globular-map G (exponential-Globular-Type I H)) →
  I → globular-map G H
ev-hom-exponential-Globular-Type = ev-hom-indexed-product-Globular-Type
```

### Binding families of globular maps

```agda
bind-family-globular-maps :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {G : Globular-Type l2 l3} {H : Globular-Type l4 l5}
  (f : I → globular-map G H) → globular-map G (exponential-Globular-Type I H)
bind-family-globular-maps = bind-indexed-family-globular-maps
```
