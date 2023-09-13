# Free groups with one generator

```agda
module group-theory.free-groups-with-one-generator where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.integers

open import foundation.action-on-identifications-functions
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.integer-powers-of-elements-groups

open import structured-types.initial-pointed-type-equipped-with-automorphism
```

</details>

## Idea

A group `F` equipped with an element `x : F` is said to satisfy the universal
property of the free group with one generator if for every group `G` the map

```text
  type-hom-Group F G → type-Group G
```

given by `h ↦ h x` is an equivalence. The group of integers is a free group with
one generator.

## Definitions

```agda
ev-element-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (g : type-Group G) →
  type-hom-Group G H → type-Group H
ev-element-hom-Group G H g f = map-hom-Group G H f g

is-free-group-with-one-generator :
  {l1 : Level} (F : Group l1) (x : type-Group F) → UUω
is-free-group-with-one-generator F x =
  {l2 : Level} (G : Group l2) → is-equiv (ev-element-hom-Group F G x)
```

## Properties

### The group of integers is the free group with one generator

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  map-hom-element-Group : ℤ → type-Group G
  map-hom-element-Group k = integer-power-Group G k g

  preserves-unit-hom-element-Group :
    map-hom-element-Group zero-ℤ ＝ unit-Group G
  preserves-unit-hom-element-Group = integer-power-zero-Group G g

  preserves-mul-map-hom-element-Group :
    (x y : ℤ) →
    ( map-hom-element-Group (x +ℤ y)) ＝
    ( mul-Group G (map-hom-element-Group x) (map-hom-element-Group y))
  preserves-mul-map-hom-element-Group =
    distributive-integer-power-add-Group G g

  hom-element-Group : type-hom-Group ℤ-Group G
  pr1 hom-element-Group = map-hom-element-Group
  pr2 hom-element-Group = preserves-mul-map-hom-element-Group

  htpy-hom-element-Group :
    (h : type-hom-Group ℤ-Group G) → map-hom-Group ℤ-Group G h one-ℤ ＝ g →
    htpy-hom-Group ℤ-Group G hom-element-Group h
  htpy-hom-element-Group h p =
    htpy-map-ℤ-Pointed-Type-With-Aut
      ( pair (pointed-type-Group G) (equiv-mul-Group G g))
      ( pair
        ( map-hom-Group ℤ-Group G h)
        ( pair
          ( preserves-unit-hom-Group ℤ-Group G h)
          ( λ x →
            ( ap
              ( map-hom-Group ℤ-Group G h)
              ( is-left-add-one-succ-ℤ x)) ∙
            ( ( preserves-mul-hom-Group ℤ-Group G h one-ℤ x) ∙
              ( ap ( mul-Group' G (map-hom-Group ℤ-Group G h x)) p)))))

  is-contr-total-hom-element-Group :
    is-contr
      ( Σ ( type-hom-Group ℤ-Group G)
          ( λ h → map-hom-Group ℤ-Group G h one-ℤ ＝ g))
  pr1 (pr1 is-contr-total-hom-element-Group) =
    hom-element-Group
  pr2 (pr1 is-contr-total-hom-element-Group) =
    right-unit-law-mul-Group G g
  pr2 is-contr-total-hom-element-Group (pair h p) =
    eq-type-subtype
      ( λ f → Id-Prop (set-Group G) (map-hom-Group ℤ-Group G f one-ℤ) g)
      ( eq-htpy-hom-Group ℤ-Group G
        ( htpy-hom-element-Group h p))

abstract
  is-free-group-with-one-generator-ℤ :
    is-free-group-with-one-generator ℤ-Group one-ℤ
  is-free-group-with-one-generator-ℤ G =
    is-equiv-is-contr-map (is-contr-total-hom-element-Group G)
```
