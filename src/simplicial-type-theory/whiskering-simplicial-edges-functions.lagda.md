# Whiskering operations on simplicial edges between functions

```agda
module simplicial-type-theory.whiskering-simplicial-edges-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-of-maps

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.horizontal-composition-simplicial-arrows-functions
open import simplicial-type-theory.horizontal-composition-simplicial-edges-functions
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.simplicial-edges
```

</details>

## Idea

Given a simplicial edge `α : f →₂ f'` of functions `A → B` we may whisker it on
the left by a function `h : B → C` to obtain a simplicial edge of functions
`hα : hf →₂ hf'`, or we may whisker it on the right by a function `g : C → A` to
obtain a simplicial edge of functions `αg : fg →₂ f'g`.

## Definitions

### Left whiskering simplicial edges between functions by functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  left-whisker-comp-simplicial-hom :
    (h : B → C) {f f' : A → B} → f →₂ f' → h ∘ f →₂ h ∘ f'
  left-whisker-comp-simplicial-hom h =
    horizontal-comp-simplicial-hom (id-simplicial-hom h)
```

### Right whiskering simplicial edges between functions by functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  right-whisker-comp-simplicial-hom :
    {f f' : A → B} → f →₂ f' → (g : C → A) → f ∘ g →₂ f' ∘ g
  right-whisker-comp-simplicial-hom α g =
    horizontal-comp-simplicial-hom α (id-simplicial-hom g)
```

## Properties

### Unit laws of whiskering of simplicial edges

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  left-unit-law-left-whisker-comp-simplicial-hom :
    {f f' : A → B} (α : f →₂ f') →
    left-whisker-comp-simplicial-hom id α ＝ α
  left-unit-law-left-whisker-comp-simplicial-hom =
    left-unit-law-horizontal-comp-simplicial-hom

  right-unit-law-right-whisker-comp-simplicial-hom :
    {f f' : A → B} (α : f →₂ f') →
    right-whisker-comp-simplicial-hom α id ＝ α
  right-unit-law-right-whisker-comp-simplicial-hom =
    right-unit-law-horizontal-comp-simplicial-hom
```

### Absorption laws of whiskering of simplicial edges

These laws hold strictly.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  right-absorption-law-left-whisker-comp-simplicial-hom :
    (g : B → C) (f : A → B) →
    left-whisker-comp-simplicial-hom g (id-simplicial-hom f) ＝
    id-simplicial-hom (g ∘ f)
  right-absorption-law-left-whisker-comp-simplicial-hom g f = refl

  left-absorption-law-right-whisker-comp-simplicial-hom :
    (g : B → C) (f : A → B) →
    right-whisker-comp-simplicial-hom (id-simplicial-hom g) f ＝
    id-simplicial-hom (g ∘ f)
  left-absorption-law-right-whisker-comp-simplicial-hom g f = refl
```

### Whiskering of simplicial edges between functions preserves function composition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  preserves-comp-left-whisker-comp-simplicial-hom :
    (h : C → D) (g : B → C) {f f' : A → B} (α : f →₂ f') →
    left-whisker-comp-simplicial-hom (h ∘ g) α ＝
    left-whisker-comp-simplicial-hom h (left-whisker-comp-simplicial-hom g α)
  preserves-comp-left-whisker-comp-simplicial-hom h g (α , refl , refl) = refl

  preserves-comp-right-whisker-comp-simplicial-hom :
    {h h' : C → D} (α : h →₂ h') (g : B → C) (f : A → B) →
    right-whisker-comp-simplicial-hom α (g ∘ f) ＝
    right-whisker-comp-simplicial-hom (right-whisker-comp-simplicial-hom α g) f
  preserves-comp-right-whisker-comp-simplicial-hom (α , refl , refl) g f = refl
```
