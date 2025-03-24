# Conjugation in higher groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module higher-group-theory.conjugation
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import higher-group-theory.higher-groups funext univalence truncations
open import higher-group-theory.homomorphisms-higher-groups funext univalence truncations

open import structured-types.conjugation-pointed-types funext univalence truncations

open import synthetic-homotopy-theory.conjugation-loops funext univalence truncations
```

</details>

## Idea

The **conjugation homomorphism** on an
[∞-group](higher-group-theory.higher-groups.md) `G` is the
[conjugation map](structured-types.conjugation-pointed-types.md) of its
classifying [pointed type](structured-types.pointed-types.md) `BG`.

## Definition

```agda
module _
  {l : Level} (G : ∞-Group l) (g : type-∞-Group G)
  where

  conjugation-∞-Group : hom-∞-Group G G
  conjugation-∞-Group =
    conjugation-Pointed-Type (classifying-pointed-type-∞-Group G) g

  classifying-map-conjugation-∞-Group :
    classifying-type-∞-Group G → classifying-type-∞-Group G
  classifying-map-conjugation-∞-Group =
    classifying-map-hom-∞-Group G G conjugation-∞-Group

  preserves-point-classifying-map-conjugation-∞-Group :
    classifying-map-conjugation-∞-Group (shape-∞-Group G) ＝ shape-∞-Group G
  preserves-point-classifying-map-conjugation-∞-Group =
    preserves-point-classifying-map-hom-∞-Group G G conjugation-∞-Group

  map-conjugation-∞-Group : type-∞-Group G → type-∞-Group G
  map-conjugation-∞-Group = map-hom-∞-Group G G conjugation-∞-Group

  compute-map-conjugation-∞-Group :
    map-conjugation-Ω g ~ map-conjugation-∞-Group
  compute-map-conjugation-∞-Group =
    htpy-compute-action-on-loops-conjugation-Pointed-Type
      ( g)
```
