# Functors between nonunital precategories

```agda
module category-theory.functors-nonunital-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-set-magmoids
open import category-theory.maps-set-magmoids
open import category-theory.nonunital-precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **functor** from a [precategory](category-theory.precategories.md) `C` to a
precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms, such that the following
  identity holds:
- `F₁ (g ∘ f) = F₁ g ∘ F₁ f`.

## Definition

### functors between nonunital precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Nonunital-Precategory l1 l2)
  (D : Nonunital-Precategory l3 l4)
  where

  functor-Nonunital-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Nonunital-Precategory =
    functor-Set-Magmoid
      ( set-magmoid-Nonunital-Precategory C)
      ( set-magmoid-Nonunital-Precategory D)

  obj-functor-Nonunital-Precategory :
    functor-Nonunital-Precategory →
    obj-Nonunital-Precategory C →
    obj-Nonunital-Precategory D
  obj-functor-Nonunital-Precategory = pr1

  hom-functor-Nonunital-Precategory :
    (F : functor-Nonunital-Precategory) →
    {x y : obj-Nonunital-Precategory C} →
    (f : hom-Nonunital-Precategory C x y) →
    hom-Nonunital-Precategory D
      ( obj-functor-Nonunital-Precategory F x)
      ( obj-functor-Nonunital-Precategory F y)
  hom-functor-Nonunital-Precategory F = pr1 (pr2 F)

  map-functor-Nonunital-Precategory :
    functor-Nonunital-Precategory →
    map-Set-Magmoid
      ( set-magmoid-Nonunital-Precategory C)
      ( set-magmoid-Nonunital-Precategory D)
  pr1 (map-functor-Nonunital-Precategory F) =
    obj-functor-Nonunital-Precategory F
  pr2 (map-functor-Nonunital-Precategory F) =
    hom-functor-Nonunital-Precategory F

  preserves-comp-functor-Nonunital-Precategory :
    (F : functor-Nonunital-Precategory)
    {x y z : obj-Nonunital-Precategory C}
    (g : hom-Nonunital-Precategory C y z)
    (f : hom-Nonunital-Precategory C x y) →
    ( hom-functor-Nonunital-Precategory F
      ( comp-hom-Nonunital-Precategory C g f)) ＝
    ( comp-hom-Nonunital-Precategory D
      ( hom-functor-Nonunital-Precategory F g)
      ( hom-functor-Nonunital-Precategory F f))
  preserves-comp-functor-Nonunital-Precategory = pr2 ∘ pr2
```

## Examples

### The identity nonunital functor

There is an identity functor on any nonunital precategory.

```agda
id-functor-Nonunital-Precategory :
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2) →
  functor-Nonunital-Precategory C C
id-functor-Nonunital-Precategory C =
  id-functor-Set-Magmoid (set-magmoid-Nonunital-Precategory C)
```

### Composition of nonunital functors

Any two compatible nonunital functors can be composed to a new nonunital
functor.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Nonunital-Precategory l1 l2)
  (B : Nonunital-Precategory l3 l4)
  (C : Nonunital-Precategory l5 l6)
  (G : functor-Nonunital-Precategory B C)
  (F : functor-Nonunital-Precategory A B)
  where

  obj-comp-functor-Nonunital-Precategory :
    obj-Nonunital-Precategory A → obj-Nonunital-Precategory C
  obj-comp-functor-Nonunital-Precategory =
    obj-functor-Nonunital-Precategory B C G ∘
    obj-functor-Nonunital-Precategory A B F

  hom-comp-functor-Nonunital-Precategory :
    {x y : obj-Nonunital-Precategory A} →
    hom-Nonunital-Precategory A x y →
    hom-Nonunital-Precategory C
      ( obj-comp-functor-Nonunital-Precategory x)
      ( obj-comp-functor-Nonunital-Precategory y)
  hom-comp-functor-Nonunital-Precategory =
    hom-functor-Nonunital-Precategory B C G ∘
    hom-functor-Nonunital-Precategory A B F

  map-comp-functor-Nonunital-Precategory :
    map-Set-Magmoid
      ( set-magmoid-Nonunital-Precategory A)
      ( set-magmoid-Nonunital-Precategory C)
  pr1 map-comp-functor-Nonunital-Precategory =
    obj-comp-functor-Nonunital-Precategory
  pr2 map-comp-functor-Nonunital-Precategory =
    hom-comp-functor-Nonunital-Precategory

  preserves-comp-comp-functor-Nonunital-Precategory =
    preserves-comp-comp-functor-Set-Magmoid
      ( set-magmoid-Nonunital-Precategory A)
      ( set-magmoid-Nonunital-Precategory B)
      ( set-magmoid-Nonunital-Precategory C)
      ( G) (F)

  comp-functor-Nonunital-Precategory : functor-Nonunital-Precategory A C
  comp-functor-Nonunital-Precategory =
    comp-functor-Set-Magmoid
      ( set-magmoid-Nonunital-Precategory A)
      ( set-magmoid-Nonunital-Precategory B)
      ( set-magmoid-Nonunital-Precategory C)
      ( G) (F)
```

## Properties

### Extensionality of functors between nonunital precategories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Nonunital-Precategory l1 l2)
  (D : Nonunital-Precategory l3 l4)
  (F G : functor-Nonunital-Precategory C D)
  where

  equiv-eq-map-eq-functor-Nonunital-Precategory :
    ( F ＝ G) ≃
    ( map-functor-Nonunital-Precategory C D F ＝
      map-functor-Nonunital-Precategory C D G)
  equiv-eq-map-eq-functor-Nonunital-Precategory =
    equiv-eq-map-eq-functor-Set-Magmoid
      ( set-magmoid-Nonunital-Precategory C)
      ( set-magmoid-Nonunital-Precategory D)
      ( F) (G)

  eq-map-eq-functor-Nonunital-Precategory :
    ( F ＝ G) →
    ( map-functor-Nonunital-Precategory C D F ＝
      map-functor-Nonunital-Precategory C D G)
  eq-map-eq-functor-Nonunital-Precategory =
    map-equiv equiv-eq-map-eq-functor-Nonunital-Precategory

  eq-eq-map-functor-Nonunital-Precategory :
    ( map-functor-Nonunital-Precategory C D F ＝
      map-functor-Nonunital-Precategory C D G) →
    ( F ＝ G)
  eq-eq-map-functor-Nonunital-Precategory =
    map-inv-equiv equiv-eq-map-eq-functor-Nonunital-Precategory

  is-section-eq-eq-map-functor-Nonunital-Precategory :
    eq-map-eq-functor-Nonunital-Precategory ∘
    eq-eq-map-functor-Nonunital-Precategory ~
    id
  is-section-eq-eq-map-functor-Nonunital-Precategory =
    is-section-map-inv-equiv equiv-eq-map-eq-functor-Nonunital-Precategory

  is-retraction-eq-eq-map-functor-Nonunital-Precategory :
    eq-eq-map-functor-Nonunital-Precategory ∘
    eq-map-eq-functor-Nonunital-Precategory ~
    id
  is-retraction-eq-eq-map-functor-Nonunital-Precategory =
    is-retraction-map-inv-equiv equiv-eq-map-eq-functor-Nonunital-Precategory
```

### Categorical laws for nonunital functor composition

#### Unit laws for nonunital functor composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Nonunital-Precategory l1 l2) (D : Nonunital-Precategory l3 l4)
  (F : functor-Nonunital-Precategory C D)
  where

  left-unit-law-comp-functor-Nonunital-Precategory :
    comp-functor-Nonunital-Precategory C D D
      ( id-functor-Nonunital-Precategory D) (F) ＝
    F
  left-unit-law-comp-functor-Nonunital-Precategory =
    eq-eq-map-functor-Nonunital-Precategory C D _ _ refl

  right-unit-law-comp-functor-Nonunital-Precategory :
    comp-functor-Nonunital-Precategory C C D
      ( F) (id-functor-Nonunital-Precategory C) ＝
    F
  right-unit-law-comp-functor-Nonunital-Precategory = refl
```

#### Associativity of functor composition

```agda
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Nonunital-Precategory l1 l1')
  (B : Nonunital-Precategory l2 l2')
  (C : Nonunital-Precategory l3 l3')
  (D : Nonunital-Precategory l4 l4')
  (F : functor-Nonunital-Precategory A B)
  (G : functor-Nonunital-Precategory B C)
  (H : functor-Nonunital-Precategory C D)
  where

  associative-comp-functor-Nonunital-Precategory :
    comp-functor-Nonunital-Precategory A B D
      ( comp-functor-Nonunital-Precategory B C D H G) (F) ＝
    comp-functor-Nonunital-Precategory A C D
      ( H) (comp-functor-Nonunital-Precategory A B C G F)
  associative-comp-functor-Nonunital-Precategory =
    eq-eq-map-functor-Nonunital-Precategory A D _ _ refl
```

#### Mac Lane pentagon for nonunital functor composition

```text
    (I(GH))F ---- I((GH)F)
          /        \
         /          \
  ((IH)G)F          I(H(GF))
          \        /
            \    /
           (IH)(GF)
```

The proof remains to be formalized.

```text
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Nonunital-Precategory l1 l1')
  (B : Nonunital-Precategory l2 l2')
  (C : Nonunital-Precategory l3 l3')
  (D : Nonunital-Precategory l4 l4')
  (E : Nonunital-Precategory l4 l4')
  (F : functor-Nonunital-Precategory A B)
  (G : functor-Nonunital-Precategory B C)
  (H : functor-Nonunital-Precategory C D)
  (I : functor-Nonunital-Precategory D E)
  where

  mac-lane-pentagon-comp-functor-Nonunital-Precategory :
    coherence-pentagon-identifications
      { x =
        comp-functor-Nonunital-Precategory A B E
        ( comp-functor-Nonunital-Precategory B D E I
          ( comp-functor-Nonunital-Precategory B C D H G))
        ( F)}
      { comp-functor-Nonunital-Precategory A D E I
        ( comp-functor-Nonunital-Precategory A B D
          ( comp-functor-Nonunital-Precategory B C D H G)
          ( F))}
      { comp-functor-Nonunital-Precategory A B E
        ( comp-functor-Nonunital-Precategory B C E
          ( comp-functor-Nonunital-Precategory C D E I H)
          ( G))
        ( F)}
      { comp-functor-Nonunital-Precategory A D E
        ( I)
        ( comp-functor-Nonunital-Precategory A C D
          ( H)
          ( comp-functor-Nonunital-Precategory A B C G F))}
      { comp-functor-Nonunital-Precategory A C E
        ( comp-functor-Nonunital-Precategory C D E I H)
        ( comp-functor-Nonunital-Precategory A B C G F)}
      ( associative-comp-functor-Nonunital-Precategory A B D E
        ( F) (comp-functor-Nonunital-Precategory B C D H G) (I))
      ( ap
        ( λ p → comp-functor-Nonunital-Precategory A B E p F)
        ( inv (associative-comp-functor-Nonunital-Precategory B C D E G H I)))
      ( ap
        ( λ p → comp-functor-Nonunital-Precategory A D E I p)
        ( associative-comp-functor-Nonunital-Precategory A B C D F G H))
      ( associative-comp-functor-Nonunital-Precategory A B C E
        ( F) (G) (comp-functor-Nonunital-Precategory C D E I H))
      ( inv
        ( associative-comp-functor-Nonunital-Precategory A C D E
          (comp-functor-Nonunital-Precategory A B C G F) H I))
  mac-lane-pentagon-comp-functor-Nonunital-Precategory = {!!}
```

## External links

- [semifunctor](https://ncatlab.org/nlab/show/semifunctor) at $n$Lab
