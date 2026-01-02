# The slice above a type

```agda
module foundation.slice where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopies
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.logical-equivalences
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
open import foundation-core.type-theoretic-principle-of-choice

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
