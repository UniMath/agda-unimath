# The slice above a type

```agda
module foundation.slice where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import trees.polynomial-endofunctors
open import trees.universal-polynomial-endofunctor
```

</details>

## Idea

The slice of a category over an object X is the category of morphisms into X. A
morphism in the slice from `f : A → X` to `g : B → X` consists of a function
`h : A → B` such that the triangle `f ~ g ∘ h` commutes. We make these
definitions for types.

## Definition

### The objects of the slice category of types

```agda
Slice : (l : Level) {l1 : Level} (A : UU l1) → UU (l1 ⊔ lsuc l)
Slice l = type-polynomial-endofunctor (universal-polynomial-endofunctor l)

module _
  {l1 l2 : Level} {A : UU l1} (f : Slice l2 A)
  where

  type-Slice : UU l2
  type-Slice = pr1 f

  map-Slice : type-Slice → A
  map-Slice = pr2 f
```

## See also

- [Equivalences in the slice over a type](foundation.equivalences-slice.md)
  characterize equality of slices.
- For slices in the context of category theory see
  [`category-theory.slice-precategories`](category-theory.slice-precategories.md).
- [Lifts of types](foundation.lifts-types.md) for the same concept under a
  different name.
