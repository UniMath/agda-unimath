# Opposite large precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.opposite-large-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories funext
open import category-theory.large-precategories funext

open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.large-identity-types
open import foundation.sets funext
open import foundation.strictly-involutive-identity-types funext
open import foundation.universe-levels
```

</details>

## Idea

Let `C` be a [large precategory](category-theory.large-precategories.md), its
**opposite large precategory** `Cᵒᵖ` is given by reversing every morphism.

## Definition

### The opposite large precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (C : Large-Precategory α β)
  where

  obj-opposite-Large-Precategory : (l : Level) → UU (α l)
  obj-opposite-Large-Precategory = obj-Large-Precategory C

  hom-set-opposite-Large-Precategory :
    {l1 l2 : Level}
    (X : obj-opposite-Large-Precategory l1)
    (Y : obj-opposite-Large-Precategory l2) → Set (β l2 l1)
  hom-set-opposite-Large-Precategory X Y = hom-set-Large-Precategory C Y X

  hom-opposite-Large-Precategory :
    {l1 l2 : Level}
    (X : obj-opposite-Large-Precategory l1)
    (Y : obj-opposite-Large-Precategory l2) → UU (β l2 l1)
  hom-opposite-Large-Precategory X Y =
    type-Set (hom-set-opposite-Large-Precategory X Y)

  comp-hom-opposite-Large-Precategory :
    {l1 l2 l3 : Level}
    {X : obj-opposite-Large-Precategory l1}
    {Y : obj-opposite-Large-Precategory l2}
    {Z : obj-opposite-Large-Precategory l3} →
    hom-opposite-Large-Precategory Y Z →
    hom-opposite-Large-Precategory X Y →
    hom-opposite-Large-Precategory X Z
  comp-hom-opposite-Large-Precategory g f = comp-hom-Large-Precategory C f g

  involutive-eq-associative-comp-hom-opposite-Large-Precategory :
    {l1 l2 l3 l4 : Level}
    {X : obj-opposite-Large-Precategory l1}
    {Y : obj-opposite-Large-Precategory l2}
    {Z : obj-opposite-Large-Precategory l3}
    {W : obj-opposite-Large-Precategory l4}
    (h : hom-opposite-Large-Precategory Z W)
    (g : hom-opposite-Large-Precategory Y Z)
    (f : hom-opposite-Large-Precategory X Y) →
    comp-hom-opposite-Large-Precategory
      ( comp-hom-opposite-Large-Precategory h g)
      ( f) ＝ⁱ
    comp-hom-opposite-Large-Precategory
      ( h)
      ( comp-hom-opposite-Large-Precategory g f)
  involutive-eq-associative-comp-hom-opposite-Large-Precategory h g f =
    invⁱ (involutive-eq-associative-comp-hom-Large-Precategory C f g h)

  associative-comp-hom-opposite-Large-Precategory :
    {l1 l2 l3 l4 : Level}
    {X : obj-opposite-Large-Precategory l1}
    {Y : obj-opposite-Large-Precategory l2}
    {Z : obj-opposite-Large-Precategory l3}
    {W : obj-opposite-Large-Precategory l4}
    (h : hom-opposite-Large-Precategory Z W)
    (g : hom-opposite-Large-Precategory Y Z)
    (f : hom-opposite-Large-Precategory X Y) →
    comp-hom-opposite-Large-Precategory
      ( comp-hom-opposite-Large-Precategory h g)
      ( f) ＝
    comp-hom-opposite-Large-Precategory
      ( h)
      ( comp-hom-opposite-Large-Precategory g f)
  associative-comp-hom-opposite-Large-Precategory h g f =
    eq-involutive-eq
      ( involutive-eq-associative-comp-hom-opposite-Large-Precategory h g f)

  id-hom-opposite-Large-Precategory :
    {l1 : Level} {X : obj-opposite-Large-Precategory l1} →
    hom-opposite-Large-Precategory X X
  id-hom-opposite-Large-Precategory = id-hom-Large-Precategory C

  left-unit-law-comp-hom-opposite-Large-Precategory :
    {l1 l2 : Level}
    {X : obj-opposite-Large-Precategory l1}
    {Y : obj-opposite-Large-Precategory l2}
    (f : hom-opposite-Large-Precategory X Y) →
    comp-hom-opposite-Large-Precategory id-hom-opposite-Large-Precategory f ＝ f
  left-unit-law-comp-hom-opposite-Large-Precategory =
    right-unit-law-comp-hom-Large-Precategory C

  right-unit-law-comp-hom-opposite-Large-Precategory :
    {l1 l2 : Level}
    {X : obj-opposite-Large-Precategory l1}
    {Y : obj-opposite-Large-Precategory l2}
    (f : hom-opposite-Large-Precategory X Y) →
    comp-hom-opposite-Large-Precategory f id-hom-opposite-Large-Precategory ＝ f
  right-unit-law-comp-hom-opposite-Large-Precategory =
    left-unit-law-comp-hom-Large-Precategory C

  opposite-Large-Precategory : Large-Precategory α (λ l1 l2 → β l2 l1)
  obj-Large-Precategory opposite-Large-Precategory =
    obj-opposite-Large-Precategory
  hom-set-Large-Precategory opposite-Large-Precategory =
    hom-set-opposite-Large-Precategory
  comp-hom-Large-Precategory opposite-Large-Precategory =
    comp-hom-opposite-Large-Precategory
  id-hom-Large-Precategory opposite-Large-Precategory =
    id-hom-opposite-Large-Precategory
  involutive-eq-associative-comp-hom-Large-Precategory
    opposite-Large-Precategory =
    involutive-eq-associative-comp-hom-opposite-Large-Precategory
  left-unit-law-comp-hom-Large-Precategory opposite-Large-Precategory =
    left-unit-law-comp-hom-opposite-Large-Precategory
  right-unit-law-comp-hom-Large-Precategory opposite-Large-Precategory =
    right-unit-law-comp-hom-opposite-Large-Precategory
```

## Properties

### The opposite large precategory construction is a strict involution

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (C : Large-Precategory α β)
  where

  is-involution-opposite-Large-Precategory :
    opposite-Large-Precategory (opposite-Large-Precategory C) ＝ω C
  is-involution-opposite-Large-Precategory = reflω
```

### Computing the isomorphism sets of the opposite large precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {l1 l2 : Level}
  (C : Large-Precategory α β)
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  where

  map-compute-iso-opposite-Large-Precategory :
    iso-Large-Precategory C X Y →
    iso-Large-Precategory (opposite-Large-Precategory C) Y X
  pr1 (map-compute-iso-opposite-Large-Precategory f) =
    hom-iso-Large-Precategory C f
  pr1 (pr2 (map-compute-iso-opposite-Large-Precategory f)) =
    hom-inv-iso-Large-Precategory C f
  pr1 (pr2 (pr2 (map-compute-iso-opposite-Large-Precategory f))) =
    is-retraction-hom-inv-iso-Large-Precategory C f
  pr2 (pr2 (pr2 (map-compute-iso-opposite-Large-Precategory f))) =
    is-section-hom-inv-iso-Large-Precategory C f

  map-inv-compute-iso-opposite-Large-Precategory :
    iso-Large-Precategory (opposite-Large-Precategory C) Y X →
    iso-Large-Precategory C X Y
  pr1 (map-inv-compute-iso-opposite-Large-Precategory f) =
    hom-iso-Large-Precategory (opposite-Large-Precategory C) f
  pr1 (pr2 (map-inv-compute-iso-opposite-Large-Precategory f)) =
    hom-inv-iso-Large-Precategory (opposite-Large-Precategory C) f
  pr1 (pr2 (pr2 (map-inv-compute-iso-opposite-Large-Precategory f))) =
    is-retraction-hom-inv-iso-Large-Precategory (opposite-Large-Precategory C) f
  pr2 (pr2 (pr2 (map-inv-compute-iso-opposite-Large-Precategory f))) =
    is-section-hom-inv-iso-Large-Precategory (opposite-Large-Precategory C) f

  is-equiv-map-compute-iso-opposite-Large-Precategory :
    is-equiv (map-compute-iso-opposite-Large-Precategory)
  pr1 (pr1 is-equiv-map-compute-iso-opposite-Large-Precategory) =
    map-inv-compute-iso-opposite-Large-Precategory
  pr2 (pr1 is-equiv-map-compute-iso-opposite-Large-Precategory) = refl-htpy
  pr1 (pr2 is-equiv-map-compute-iso-opposite-Large-Precategory) =
    map-inv-compute-iso-opposite-Large-Precategory
  pr2 (pr2 is-equiv-map-compute-iso-opposite-Large-Precategory) = refl-htpy

  compute-iso-opposite-Large-Precategory :
    iso-Large-Precategory C X Y ≃
    iso-Large-Precategory (opposite-Large-Precategory C) Y X
  pr1 compute-iso-opposite-Large-Precategory =
    map-compute-iso-opposite-Large-Precategory
  pr2 compute-iso-opposite-Large-Precategory =
    is-equiv-map-compute-iso-opposite-Large-Precategory
```

## External links

- [Precategories - opposites](https://1lab.dev/Cat.Base.html#opposites) at 1lab
- [opposite category](https://ncatlab.org/nlab/show/opposite+category) at $n$Lab
- [Opposite category](https://en.wikipedia.org/wiki/Opposite_category) at
  Wikipedia
- [opposite category](https://www.wikidata.org/wiki/Q7098616) at Wikidata
