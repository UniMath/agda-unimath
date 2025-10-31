# Morphisms of magmas

```agda
module structured-types.morphisms-magmas where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.magmas
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of magmas" WD="morphism of magmas" WDID=Q77990146 Agda=hom-Magma}}
of [magmas](structured-types.magmas.md) from `M` to `N` is a map between their
underlying types that preserves the binary operation.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Magma l1) (N : Magma l2)
  where

  preserves-mul-Magma : (type-Magma M → type-Magma N) → UU (l1 ⊔ l2)
  preserves-mul-Magma f =
    (x y : type-Magma M) → f (mul-Magma M x y) ＝ mul-Magma N (f x) (f y)

  hom-Magma : UU (l1 ⊔ l2)
  hom-Magma = Σ (type-Magma M → type-Magma N) preserves-mul-Magma

  map-hom-Magma : hom-Magma → type-Magma M → type-Magma N
  map-hom-Magma = pr1

  preserves-mul-map-hom-Magma :
    (f : hom-Magma) → preserves-mul-Magma (map-hom-Magma f)
  preserves-mul-map-hom-Magma = pr2
```
