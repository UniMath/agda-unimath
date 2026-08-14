# Morphisms of unital magmas

```agda
module structured-types.morphisms-unital-magmas where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.magmas
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of unital magmas" Agda=hom-Unital-Magma}}
of [unital magmas](structured-types.magmas.md) from `M` to `N` is a map between their
underlying types that preserves the binary operation and the unit element.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Unital-Magma l1) (N : Unital-Magma l2)
  where

  preserves-mul-Unital-Magma :
    (type-Unital-Magma M → type-Unital-Magma N) → UU (l1 ⊔ l2)
  preserves-mul-Unital-Magma f =
    {x y : type-Unital-Magma M} →
    f (mul-Unital-Magma M x y) ＝ mul-Unital-Magma N (f x) (f y)

  preserves-unit-Unital-Magma :
    (type-Unital-Magma M → type-Unital-Magma N) → UU l2
  preserves-unit-Unital-Magma f =
    f (unit-Unital-Magma M) ＝ unit-Unital-Magma N

  hom-Unital-Magma : UU (l1 ⊔ l2)
  hom-Unital-Magma =
    Σ ( type-Unital-Magma M → type-Unital-Magma N)
      ( λ f → preserves-mul-Unital-Magma f × preserves-unit-Unital-Magma f)

  map-hom-Unital-Magma :
    hom-Unital-Magma → type-Unital-Magma M → type-Unital-Magma N
  map-hom-Unital-Magma = pr1

  preserves-mul-hom-Unital-Magma :
    (f : hom-Unital-Magma) → preserves-mul-Unital-Magma (map-hom-Unital-Magma f)
  preserves-mul-hom-Unital-Magma = pr1 ∘ pr2

  preserves-unit-hom-Unital-Magma :
    (f : hom-Unital-Magma) →
    preserves-unit-Unital-Magma (map-hom-Unital-Magma f)
  preserves-unit-hom-Unital-Magma = pr2 ∘ pr2
```
