# Morphisms of wild quasigroups

```agda
module structured-types.morphisms-wild-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.magmas
open import structured-types.morphisms-magmas
open import structured-types.wild-quasigroups
```

</details>

## Idea

A morphism of [wild quasigroups](structured-types.wild-quasigroups.md) `A → B`
is just a [morphism](structured-types.morphisms-magmas.md) of their underlying
[magmas](structured-types.magmas.md).

## Definition

```agda
module _
  {l1 l2 : Level} (A : Wild-Quasigroup l1) (B : Wild-Quasigroup l2)
  where

  preserves-mul-Wild-Quasigroup :
    ( type-Wild-Quasigroup A → type-Wild-Quasigroup B) → UU (l1 ⊔ l2)
  preserves-mul-Wild-Quasigroup f =
    ( x y : type-Wild-Quasigroup A) →
    f (mul-Wild-Quasigroup A x y) ＝ mul-Wild-Quasigroup B (f x) (f y)

  hom-Wild-Quasigroup : UU (l1 ⊔ l2)
  hom-Wild-Quasigroup =
    hom-Magma (magma-Wild-Quasigroup A) (magma-Wild-Quasigroup B)

  map-hom-Wild-Quasigroup :
    hom-Wild-Quasigroup → type-Wild-Quasigroup A → type-Wild-Quasigroup B
  map-hom-Wild-Quasigroup f = pr1 f

  preserves-mul-map-hom-Wild-Quasigroup :
    ( f : hom-Wild-Quasigroup) →
    preserves-mul-Wild-Quasigroup (map-hom-Wild-Quasigroup f)
  preserves-mul-map-hom-Wild-Quasigroup = pr2
```
