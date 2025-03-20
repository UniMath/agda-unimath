# Representable functors between categories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.representable-functors-categories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext
open import category-theory.functors-categories funext
open import category-theory.natural-transformations-functors-categories funext
open import category-theory.representable-functors-precategories funext

open import foundation.category-of-sets funext
open import foundation.universe-levels
```

</details>

## Idea

Given a [category](category-theory.categories.md) `C` and an object `c`, there
is a [functor](category-theory.functors-categories.md) from `C` to the
[category of sets](foundation.category-of-sets.md) **represented** by `c` that:

- sends an object `x` of `C` to the [set](foundation-core.sets.md) `hom c x` and
- sends a morphism `g : hom x y` of `C` to the function `hom c x → hom c y`
  defined by postcomposition with `g`.

The functoriality axioms follow, by
[function extensionality](foundation.function-extensionality.md), from
associativity and the left unit law for the category `C`.

## Definition

```agda
representable-functor-Category :
  {l1 l2 : Level} (C : Category l1 l2) (c : obj-Category C) →
  functor-Category C (Set-Category l2)
representable-functor-Category C =
  representable-functor-Precategory (precategory-Category C)
```

## Natural transformations between representable functors

A morphism `f : hom b c` in a category `C` defines a
[natural transformation](category-theory.natural-transformations-functors-categories.md)
from the functor represented by `c` to the functor represented by `b`. Its
components `hom c x → hom b x` are defined by precomposition with `f`.

```agda
representable-natural-transformation-Category :
  {l1 l2 : Level} (C : Category l1 l2) {b c : obj-Category C}
  (f : hom-Category C b c) →
  natural-transformation-Category
    ( C)
    ( Set-Category l2)
    ( representable-functor-Category C c)
    ( representable-functor-Category C b)
representable-natural-transformation-Category C =
  representable-natural-transformation-Precategory (precategory-Category C)
```
