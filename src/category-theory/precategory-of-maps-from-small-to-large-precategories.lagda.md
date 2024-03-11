# The precategory of maps and natural transformations from a small to a large precategory

```agda
module category-theory.precategory-of-maps-from-small-to-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.maps-from-small-to-large-precategories
open import category-theory.natural-transformations-maps-from-small-to-large-precategories
open import category-theory.precategories

open import foundation.identity-types
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

[Maps](category-theory.maps-from-small-to-large-precategories.md) from
[(small) precategories](category-theory.precategories.md) to
[large precategories](category-theory.large-precategories.md) and
[natural transformations](category-theory.natural-transformations-maps-precategories.md)
between them introduce a new large precategory whose identity map and
composition structure are inherited pointwise from the codomain precategory.
This is called the **precategory of maps from a small to a large precategory**.

## Definitions

### The large precategory of maps and natural transformations from a small to a large precategory

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  where

  comp-hom-map-large-precategory-Small-Large-Precategory :
    {γF γG γH : Level}
    {F : map-Small-Large-Precategory C D γF}
    {G : map-Small-Large-Precategory C D γG}
    {H : map-Small-Large-Precategory C D γH} →
    natural-transformation-map-Small-Large-Precategory C D G H →
    natural-transformation-map-Small-Large-Precategory C D F G →
    natural-transformation-map-Small-Large-Precategory C D F H
  comp-hom-map-large-precategory-Small-Large-Precategory {F = F} {G} {H} =
    comp-natural-transformation-map-Small-Large-Precategory C D F G H

  associative-comp-hom-map-large-precategory-Small-Large-Precategory :
    {γF γG γH γI : Level}
    {F : map-Small-Large-Precategory C D γF}
    {G : map-Small-Large-Precategory C D γG}
    {H : map-Small-Large-Precategory C D γH}
    {I : map-Small-Large-Precategory C D γI}
    (h : natural-transformation-map-Small-Large-Precategory C D H I)
    (g : natural-transformation-map-Small-Large-Precategory C D G H)
    (f : natural-transformation-map-Small-Large-Precategory C D F G) →
    comp-natural-transformation-map-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-map-Small-Large-Precategory C D G H I h g)
      ( f) ＝
    comp-natural-transformation-map-Small-Large-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-map-Small-Large-Precategory C D F G H g f)
  associative-comp-hom-map-large-precategory-Small-Large-Precategory
    {F = F} {G} {H} {I} h g f =
    associative-comp-natural-transformation-map-Small-Large-Precategory
      C D F G H I f g h

  involutive-eq-associative-comp-hom-map-large-precategory-Small-Large-Precategory :
    {γF γG γH γI : Level}
    {F : map-Small-Large-Precategory C D γF}
    {G : map-Small-Large-Precategory C D γG}
    {H : map-Small-Large-Precategory C D γH}
    {I : map-Small-Large-Precategory C D γI}
    (h : natural-transformation-map-Small-Large-Precategory C D H I)
    (g : natural-transformation-map-Small-Large-Precategory C D G H)
    (f : natural-transformation-map-Small-Large-Precategory C D F G) →
    comp-natural-transformation-map-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-map-Small-Large-Precategory C D G H I h g)
      ( f) ＝ⁱ
    comp-natural-transformation-map-Small-Large-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-map-Small-Large-Precategory C D F G H g f)
  involutive-eq-associative-comp-hom-map-large-precategory-Small-Large-Precategory
    {F = F} {G} {H} {I} h g f =
    involutive-eq-associative-comp-natural-transformation-map-Small-Large-Precategory
      C D F G H I f g h

  id-hom-map-large-precategory-Small-Large-Precategory :
    {γF : Level} {F : map-Small-Large-Precategory C D γF} →
    natural-transformation-map-Small-Large-Precategory C D F F
  id-hom-map-large-precategory-Small-Large-Precategory {F = F} =
    id-natural-transformation-map-Small-Large-Precategory C D F

  left-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory :
    {γF γG : Level}
    {F : map-Small-Large-Precategory C D γF}
    {G : map-Small-Large-Precategory C D γG}
    (a : natural-transformation-map-Small-Large-Precategory C D F G) →
    ( comp-natural-transformation-map-Small-Large-Precategory C D F G G
      ( id-natural-transformation-map-Small-Large-Precategory C D G) a) ＝
    ( a)
  left-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory
    { F = F} {G} =
    left-unit-law-comp-natural-transformation-map-Small-Large-Precategory
      C D F G

  right-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory :
    {γF γG : Level}
    {F : map-Small-Large-Precategory C D γF}
    {G : map-Small-Large-Precategory C D γG}
    (a : natural-transformation-map-Small-Large-Precategory C D F G) →
    ( comp-natural-transformation-map-Small-Large-Precategory C D F F G
        a (id-natural-transformation-map-Small-Large-Precategory C D F)) ＝
    ( a)
  right-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory
    { F = F} {G} =
    right-unit-law-comp-natural-transformation-map-Small-Large-Precategory
      C D F G

  map-large-precategory-Small-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ α l ⊔ β l l) (λ l l' → l1 ⊔ l2 ⊔ β l l')
  obj-Large-Precategory map-large-precategory-Small-Large-Precategory =
    map-Small-Large-Precategory C D
  hom-set-Large-Precategory map-large-precategory-Small-Large-Precategory =
    natural-transformation-map-set-Small-Large-Precategory C D
  comp-hom-Large-Precategory map-large-precategory-Small-Large-Precategory =
    comp-hom-map-large-precategory-Small-Large-Precategory
  id-hom-Large-Precategory map-large-precategory-Small-Large-Precategory =
    id-hom-map-large-precategory-Small-Large-Precategory
  involutive-eq-associative-comp-hom-Large-Precategory
    map-large-precategory-Small-Large-Precategory =
    involutive-eq-associative-comp-hom-map-large-precategory-Small-Large-Precategory
  left-unit-law-comp-hom-Large-Precategory
    map-large-precategory-Small-Large-Precategory =
    left-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory
  right-unit-law-comp-hom-Large-Precategory
    map-large-precategory-Small-Large-Precategory =
    right-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory
```

### The small precategories of maps and natural transformations from a small to a large precategory

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  where

  map-precategory-Small-Large-Precategory :
    (l : Level) → Precategory (l1 ⊔ l2 ⊔ α l ⊔ β l l) (l1 ⊔ l2 ⊔ β l l)
  map-precategory-Small-Large-Precategory =
    precategory-Large-Precategory
      ( map-large-precategory-Small-Large-Precategory C D)
```
