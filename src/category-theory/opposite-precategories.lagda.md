# Opposite precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.opposite-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories funext
open import category-theory.precategories funext

open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.involutions funext
open import foundation.sets funext
open import foundation.strictly-involutive-identity-types funext
open import foundation.universe-levels
```

</details>

## Idea

Let `C` be a [precategory](category-theory.precategories.md), its **opposite
precategory** `Cᵒᵖ` is given by reversing every morphism.

## Definition

### The opposite precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  obj-opposite-Precategory : UU l1
  obj-opposite-Precategory = obj-Precategory C

  hom-set-opposite-Precategory : (x y : obj-opposite-Precategory) → Set l2
  hom-set-opposite-Precategory x y = hom-set-Precategory C y x

  hom-opposite-Precategory : (x y : obj-opposite-Precategory) → UU l2
  hom-opposite-Precategory x y = type-Set (hom-set-opposite-Precategory x y)

  comp-hom-opposite-Precategory :
    {x y z : obj-opposite-Precategory} →
    hom-opposite-Precategory y z →
    hom-opposite-Precategory x y →
    hom-opposite-Precategory x z
  comp-hom-opposite-Precategory g f = comp-hom-Precategory C f g

  involutive-eq-associative-comp-hom-opposite-Precategory :
    {x y z w : obj-opposite-Precategory}
    (h : hom-opposite-Precategory z w)
    (g : hom-opposite-Precategory y z)
    (f : hom-opposite-Precategory x y) →
    ( comp-hom-opposite-Precategory (comp-hom-opposite-Precategory h g) f) ＝ⁱ
    ( comp-hom-opposite-Precategory h (comp-hom-opposite-Precategory g f))
  involutive-eq-associative-comp-hom-opposite-Precategory h g f =
    invⁱ (involutive-eq-associative-comp-hom-Precategory C f g h)

  associative-comp-hom-opposite-Precategory :
    {x y z w : obj-opposite-Precategory}
    (h : hom-opposite-Precategory z w)
    (g : hom-opposite-Precategory y z)
    (f : hom-opposite-Precategory x y) →
    ( comp-hom-opposite-Precategory (comp-hom-opposite-Precategory h g) f) ＝
    ( comp-hom-opposite-Precategory h (comp-hom-opposite-Precategory g f))
  associative-comp-hom-opposite-Precategory h g f =
    eq-involutive-eq
      ( involutive-eq-associative-comp-hom-opposite-Precategory h g f)

  id-hom-opposite-Precategory :
    {x : obj-opposite-Precategory} → hom-opposite-Precategory x x
  id-hom-opposite-Precategory = id-hom-Precategory C

  left-unit-law-comp-hom-opposite-Precategory :
    {x y : obj-opposite-Precategory}
    (f : hom-opposite-Precategory x y) →
    comp-hom-opposite-Precategory id-hom-opposite-Precategory f ＝ f
  left-unit-law-comp-hom-opposite-Precategory =
    right-unit-law-comp-hom-Precategory C

  right-unit-law-comp-hom-opposite-Precategory :
    {x y : obj-opposite-Precategory} (f : hom-opposite-Precategory x y) →
    comp-hom-opposite-Precategory f id-hom-opposite-Precategory ＝ f
  right-unit-law-comp-hom-opposite-Precategory =
    left-unit-law-comp-hom-Precategory C

  opposite-Precategory : Precategory l1 l2
  pr1 opposite-Precategory = obj-opposite-Precategory
  pr1 (pr2 opposite-Precategory) = hom-set-opposite-Precategory
  pr1 (pr1 (pr2 (pr2 opposite-Precategory))) = comp-hom-opposite-Precategory
  pr2 (pr1 (pr2 (pr2 opposite-Precategory))) =
    involutive-eq-associative-comp-hom-opposite-Precategory
  pr1 (pr2 (pr2 (pr2 opposite-Precategory))) x = id-hom-opposite-Precategory {x}
  pr1 (pr2 (pr2 (pr2 (pr2 opposite-Precategory)))) =
    left-unit-law-comp-hom-opposite-Precategory
  pr2 (pr2 (pr2 (pr2 (pr2 opposite-Precategory)))) =
    right-unit-law-comp-hom-opposite-Precategory
```

## Properties

### The opposite construction is a definitional involution on the type of precategories

```agda
is-involution-opposite-Precategory :
  {l1 l2 : Level} → is-involution (opposite-Precategory {l1} {l2})
is-involution-opposite-Precategory C = refl

involution-opposite-Precategory :
  (l1 l2 : Level) → involution (Precategory l1 l2)
pr1 (involution-opposite-Precategory l1 l2) = opposite-Precategory
pr2 (involution-opposite-Precategory l1 l2) = is-involution-opposite-Precategory

is-equiv-opposite-Precategory :
  {l1 l2 : Level} → is-equiv (opposite-Precategory {l1} {l2})
is-equiv-opposite-Precategory =
  is-equiv-is-involution is-involution-opposite-Precategory

equiv-opposite-Precategory :
  (l1 l2 : Level) → Precategory l1 l2 ≃ Precategory l1 l2
equiv-opposite-Precategory l1 l2 =
  equiv-involution (involution-opposite-Precategory l1 l2)
```

### Computing the isomorphism sets of the opposite precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) {x y : obj-Precategory C}
  where

  map-compute-iso-opposite-Precategory :
    iso-Precategory C x y → iso-Precategory (opposite-Precategory C) y x
  pr1 (map-compute-iso-opposite-Precategory f) =
    hom-iso-Precategory C f
  pr1 (pr2 (map-compute-iso-opposite-Precategory f)) =
    hom-inv-iso-Precategory C f
  pr1 (pr2 (pr2 (map-compute-iso-opposite-Precategory f))) =
    is-retraction-hom-inv-iso-Precategory C f
  pr2 (pr2 (pr2 (map-compute-iso-opposite-Precategory f))) =
    is-section-hom-inv-iso-Precategory C f

  map-inv-compute-iso-opposite-Precategory :
    iso-Precategory (opposite-Precategory C) y x → iso-Precategory C x y
  pr1 (map-inv-compute-iso-opposite-Precategory f) =
    hom-iso-Precategory (opposite-Precategory C) f
  pr1 (pr2 (map-inv-compute-iso-opposite-Precategory f)) =
    hom-inv-iso-Precategory (opposite-Precategory C) f
  pr1 (pr2 (pr2 (map-inv-compute-iso-opposite-Precategory f))) =
    is-retraction-hom-inv-iso-Precategory (opposite-Precategory C) f
  pr2 (pr2 (pr2 (map-inv-compute-iso-opposite-Precategory f))) =
    is-section-hom-inv-iso-Precategory (opposite-Precategory C) f

  is-equiv-map-compute-iso-opposite-Precategory :
    is-equiv (map-compute-iso-opposite-Precategory)
  pr1 (pr1 is-equiv-map-compute-iso-opposite-Precategory) =
    map-inv-compute-iso-opposite-Precategory
  pr2 (pr1 is-equiv-map-compute-iso-opposite-Precategory) = refl-htpy
  pr1 (pr2 is-equiv-map-compute-iso-opposite-Precategory) =
    map-inv-compute-iso-opposite-Precategory
  pr2 (pr2 is-equiv-map-compute-iso-opposite-Precategory) = refl-htpy

  compute-iso-opposite-Precategory :
    iso-Precategory C x y ≃ iso-Precategory (opposite-Precategory C) y x
  pr1 compute-iso-opposite-Precategory =
    map-compute-iso-opposite-Precategory
  pr2 compute-iso-opposite-Precategory =
    is-equiv-map-compute-iso-opposite-Precategory
```

## External links

- [Precategories - opposites](https://1lab.dev/Cat.Base.html#opposites) at 1lab
- [opposite category](https://ncatlab.org/nlab/show/opposite+category) at $n$Lab
- [Opposite category](https://en.wikipedia.org/wiki/Opposite_category) at
  Wikipedia
- [opposite category](https://www.wikidata.org/wiki/Q7098616) at Wikidata
