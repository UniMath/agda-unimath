# Conjugation on concrete groups

```agda
module group-theory.conjugation-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.conjugation
open import group-theory.homomorphisms-concrete-groups

open import higher-group-theory.conjugation
```

</details>

## Idea

The **conjugation operation** on a
[concrete group](group-theory.concrete-groups.md) `G` can be seen as a
[homomorphism](group-theory.homomorphisms-concrete-groups.md) of concrete groups
and as a [concrete group action](group-theory.concrete-group-actions.md).

Note that the delooping of the
[conjugation homomorphism](structured-types.conjugation-pointed-types.md) can be
defined directly for [pointed types](structured-types.pointed-types.md), which
applies also to the case of [∞-groups](higher-group-theory.higher-groups.md).

## Definitions

### The conjugation homomorphism on concrete groups

```agda
module _
  {l : Level} (G : Concrete-Group l) (g : type-Concrete-Group G)
  where

  conjugation-Concrete-Group : hom-Concrete-Group G G
  conjugation-Concrete-Group = conjugation-∞-Group (∞-group-Concrete-Group G) g

  classifying-map-conjugation-Concrete-Group :
    classifying-type-Concrete-Group G → classifying-type-Concrete-Group G
  classifying-map-conjugation-Concrete-Group =
    classifying-map-hom-Concrete-Group G G conjugation-Concrete-Group

  preserves-point-classifying-map-conjugation-Concrete-Group :
    classifying-map-conjugation-Concrete-Group (shape-Concrete-Group G) ＝
    shape-Concrete-Group G
  preserves-point-classifying-map-conjugation-Concrete-Group =
    preserves-point-classifying-map-hom-Concrete-Group G G
      ( conjugation-Concrete-Group)

  map-conjugation-Concrete-Group :
    type-Concrete-Group G → type-Concrete-Group G
  map-conjugation-Concrete-Group =
    map-hom-Concrete-Group G G conjugation-Concrete-Group

  compute-map-conjugation-Concrete-Group :
    conjugation-Group' (abstract-group-Concrete-Group G) g ~
    map-conjugation-Concrete-Group
  compute-map-conjugation-Concrete-Group x =
    ( assoc (inv g) x g) ∙
    ( compute-map-conjugation-∞-Group (∞-group-Concrete-Group G) g x)
```
