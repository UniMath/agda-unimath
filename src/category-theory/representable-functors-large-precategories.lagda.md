# Representable functors between large precategories

```agda
module category-theory.representable-functors-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-transformations-functors-large-precategories

open import foundation.category-of-sets
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a [large precategory](category-theory.large-precategories.md) `C` and an
object `c`, there is a
[functor](category-theory.functors-large-precategories.md) from `C` to the
[precategory of sets](foundation.category-of-sets.md) **represented** by `c`
that:

- sends an object `x` of `C` to the [set](foundation-core.sets.md) `hom c x` and
- sends a morphism `g : hom x y` of `C` to the function `hom c x → hom c y`
  defined by postcomposition with `g`.

The functoriality axioms follow, by
[function extensionality](foundation.function-extensionality.md), from
associativity and the left unit law for the precategory `C`.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 : Level} (c : obj-Large-Precategory C l1)
  where

  obj-representable-functor-Large-Precategory :
    {l2 : Level} (x : obj-Large-Precategory C l2) → Set (β l1 l2)
  obj-representable-functor-Large-Precategory =
    hom-set-Large-Precategory C c

  hom-representable-functor-Large-Precategory :
    {l2 l3 : Level}
    {X : obj-Large-Precategory C l2} {Y : obj-Large-Precategory C l3} →
    hom-Large-Precategory C X Y →
    hom-Set
      ( obj-representable-functor-Large-Precategory X)
      ( obj-representable-functor-Large-Precategory Y)
  hom-representable-functor-Large-Precategory =
    postcomp-hom-Large-Precategory C c

  preserves-comp-representable-functor-Large-Precategory :
    {l2 l3 l4 : Level}
    {X : obj-Large-Precategory C l2}
    {Y : obj-Large-Precategory C l3}
    {Z : obj-Large-Precategory C l4}
    (g : hom-Large-Precategory C Y Z)
    (f : hom-Large-Precategory C X Y) →
    hom-representable-functor-Large-Precategory
      ( comp-hom-Large-Precategory C g f) ＝
    hom-representable-functor-Large-Precategory g ∘
    hom-representable-functor-Large-Precategory f
  preserves-comp-representable-functor-Large-Precategory g f =
    eq-htpy (associative-comp-hom-Large-Precategory C g f)

  preserves-id-representable-functor-Large-Precategory :
    {l2 : Level} {X : obj-Large-Precategory C l2} →
    hom-representable-functor-Large-Precategory
      ( id-hom-Large-Precategory C {X = X}) ＝
    id
  preserves-id-representable-functor-Large-Precategory =
    eq-htpy (left-unit-law-comp-hom-Large-Precategory C)

  representable-functor-Large-Precategory :
    functor-Large-Precategory (β l1) C (Set-Large-Precategory)
  obj-functor-Large-Precategory representable-functor-Large-Precategory =
    obj-representable-functor-Large-Precategory
  hom-functor-Large-Precategory representable-functor-Large-Precategory =
    hom-representable-functor-Large-Precategory
  preserves-comp-functor-Large-Precategory
    representable-functor-Large-Precategory =
    preserves-comp-representable-functor-Large-Precategory
  preserves-id-functor-Large-Precategory
    representable-functor-Large-Precategory =
    preserves-id-representable-functor-Large-Precategory
```

## Natural transformations between representable functors

A morphism `f : hom b c` in a large precategory `C` defines a
[natural transformation](category-theory.natural-transformations-functors-large-precategories.md)
from the functor represented by `c` to the functor represented by `b`. Its
components `hom c x → hom b x` are defined by precomposition with `f`.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (C : Large-Precategory α β)
  {l1 l2 : Level}
  (b : obj-Large-Precategory C l1) (c : obj-Large-Precategory C l2)
  (f : hom-Large-Precategory C b c)
  where

  hom-representable-natural-transformation-Large-Precategory :
    family-of-morphisms-functor-Large-Precategory C Set-Large-Precategory
      ( representable-functor-Large-Precategory C c)
      ( representable-functor-Large-Precategory C b)
  hom-representable-natural-transformation-Large-Precategory =
    precomp-hom-Large-Precategory C f

  naturality-representable-natural-transformation-Large-Precategory :
    naturality-family-of-morphisms-functor-Large-Precategory C
      ( Set-Large-Precategory)
      ( representable-functor-Large-Precategory C c)
      ( representable-functor-Large-Precategory C b)
      ( hom-representable-natural-transformation-Large-Precategory)
  naturality-representable-natural-transformation-Large-Precategory h =
    inv (eq-htpy (λ g → associative-comp-hom-Large-Precategory C h g f))

  representable-natural-transformation-Large-Precategory :
    natural-transformation-Large-Precategory C Set-Large-Precategory
      ( representable-functor-Large-Precategory C c)
      ( representable-functor-Large-Precategory C b)
  hom-natural-transformation-Large-Precategory
    representable-natural-transformation-Large-Precategory =
    hom-representable-natural-transformation-Large-Precategory
  naturality-natural-transformation-Large-Precategory
    representable-natural-transformation-Large-Precategory =
    naturality-representable-natural-transformation-Large-Precategory
```
