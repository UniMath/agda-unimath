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
open import foundation.homotopies
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
representable-functor-Large-Precategory :
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l : Level} (c : obj-Large-Precategory C l) →
  functor-Large-Precategory C (Set-Large-Precategory) (β l)
obj-functor-Large-Precategory (representable-functor-Large-Precategory C c) =
  hom-set-Large-Precategory C c
hom-functor-Large-Precategory (representable-functor-Large-Precategory C c) g =
  postcomp-hom-Large-Precategory C c g
preserves-comp-functor-Large-Precategory
  ( representable-functor-Large-Precategory C c) h g =
  eq-htpy (associative-comp-hom-Large-Precategory C h g)
preserves-id-functor-Large-Precategory
  ( representable-functor-Large-Precategory C c) =
  eq-htpy (left-unit-law-comp-hom-Large-Precategory C)
```

## Natural transformations between representable functors

A morphism `f : hom b c` in a large precategory `C` defines a
[natural transformation](category-theory.natural-transformations-functors-large-precategories.md)
from the functor represented by `c` to the functor represented by `b`. Its
components `hom c x → hom b x` are defined by precomposition with `f`.

```agda
representable-natural-transformation-Large-Precategory :
  {α : Level → Level} {β : Level → Level → Level} (C : Large-Precategory α β)
  {l1 l2 : Level}
  (b : obj-Large-Precategory C l1) (c : obj-Large-Precategory C l2)
  (f : hom-Large-Precategory C b c) →
  natural-transformation-Large-Precategory
    ( representable-functor-Large-Precategory C c)
    ( representable-functor-Large-Precategory C b)
hom-family-natural-transformation-Large-Precategory
  ( representable-natural-transformation-Large-Precategory C b c f) =
  precomp-hom-Large-Precategory C f
coherence-square-natural-transformation-Large-Precategory
  ( representable-natural-transformation-Large-Precategory C b c f) h =
  eq-htpy (inv-htpy (λ g → associative-comp-hom-Large-Precategory C h g f))
```
