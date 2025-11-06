# Batanin systems in globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.batanin-systems-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.universe-levels

open import globular-types.globular-types

open import lists.lists

open import trees.plane-trees
```

</details>

## Idea

A
{{#concept "Batanin system" Disambiguation="globular types" Agda=batanin-system-Globular-Type}}
is an internal definition of a
[pasting diagram](globular-types.globular-pasting-diagrams.md) of
[globular types](globular-types.globular-types.md).

## Definition

### Batanin systems

```agda
module _
  {l1 : Level}
  where

  mutual
    batanin-system-Globular-Type :
      (T : listed-plane-tree) (G : Globular-Type l1 l1) → UU l1
    batanin-system-Globular-Type (make-listed-plane-tree nil) G =
      0-cell-Globular-Type G
    batanin-system-Globular-Type (make-listed-plane-tree (cons T ℓ)) G =
      Σ ( 0-cell-Globular-Type G)
        ( λ x →
          Σ ( batanin-system-Globular-Type (make-listed-plane-tree ℓ) G)
            ( λ B →
              batanin-system-Globular-Type T
                ( 1-cell-globular-type-Globular-Type G
                  ( x)
                  ( source-cell-batanin-system-Globular-Type
                    ( make-listed-plane-tree ℓ)
                    ( G)
                    ( B)))))

    source-cell-batanin-system-Globular-Type :
      (T : listed-plane-tree) (G : Globular-Type l1 l1)
      (B : batanin-system-Globular-Type T G) → 0-cell-Globular-Type G
    source-cell-batanin-system-Globular-Type (make-listed-plane-tree nil) G B =
      B
    source-cell-batanin-system-Globular-Type
      ( make-listed-plane-tree (cons T ℓ))
      ( G)
      ( B) =
      pr1 B
```
