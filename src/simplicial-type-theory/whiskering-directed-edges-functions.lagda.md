# Whiskering operations on directed edges between functions

```agda
module simplicial-type-theory.whiskering-directed-edges-functions where
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

open import orthogonal-factorization-systems.extensions-maps

open import simplicial-type-theory.arrows
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type I
open import simplicial-type-theory.horizontal-composition-arrows-functions
open import simplicial-type-theory.horizontal-composition-directed-edges-functions
```

</details>

## Idea

Given a directed edge `α : f →▵ f'` of functions in `A → B` we may whisker it on
the left by a function `h : B → C` to obtain a directed edge of functions
`hα : hf →▵ hf'`, or we may whisker it on the right by a function `g : C → A` to
obtain a directed edge of functions `αg : fg →▵ f'g`.

## Definitions

### Left whiskering directed edges between functions by functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  left-whisker-comp-hom▵ :
    (h : B → C) {f f' : A → B} → f →▵ f' → h ∘ f →▵ h ∘ f'
  left-whisker-comp-hom▵ h =
    horizontal-comp-hom▵ (id-hom▵ h)
```

### Right whiskering directed edges between functions by functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  right-whisker-comp-hom▵ :
    {f f' : A → B} → f →▵ f' → (g : C → A) → f ∘ g →▵ f' ∘ g
  right-whisker-comp-hom▵ α g =
    horizontal-comp-hom▵ α (id-hom▵ g)
```

## Properties

### Unit laws of whiskering of directed edges

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  left-unit-law-left-whisker-comp-hom▵ :
    {f f' : A → B} (α : f →▵ f') →
    left-whisker-comp-hom▵ id α ＝ α
  left-unit-law-left-whisker-comp-hom▵ =
    left-unit-law-horizontal-comp-hom▵

  right-unit-law-right-whisker-comp-hom▵ :
    {f f' : A → B} (α : f →▵ f') →
    right-whisker-comp-hom▵ α id ＝ α
  right-unit-law-right-whisker-comp-hom▵ =
    right-unit-law-horizontal-comp-hom▵
```

### Absorption laws of whiskering of directed edges

These laws hold strictly.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  right-absorption-law-left-whisker-comp-hom▵ :
    (g : B → C) (f : A → B) →
    left-whisker-comp-hom▵ g (id-hom▵ f) ＝
    id-hom▵ (g ∘ f)
  right-absorption-law-left-whisker-comp-hom▵ g f = refl

  left-absorption-law-right-whisker-comp-hom▵ :
    (g : B → C) (f : A → B) →
    right-whisker-comp-hom▵ (id-hom▵ g) f ＝
    id-hom▵ (g ∘ f)
  left-absorption-law-right-whisker-comp-hom▵ g f = refl
```

### Whiskering of directed edges between functions preserves function composition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  preserves-comp-left-whisker-comp-hom▵ :
    (h : C → D) (g : B → C) {f f' : A → B} (α : f →▵ f') →
    left-whisker-comp-hom▵ (h ∘ g) α ＝
    left-whisker-comp-hom▵ h (left-whisker-comp-hom▵ g α)
  preserves-comp-left-whisker-comp-hom▵ h g (α , refl , refl) = refl

  preserves-comp-right-whisker-comp-hom▵ :
    {h h' : C → D} (α : h →▵ h') (g : B → C) (f : A → B) →
    right-whisker-comp-hom▵ α (g ∘ f) ＝
    right-whisker-comp-hom▵ (right-whisker-comp-hom▵ α g) f
  preserves-comp-right-whisker-comp-hom▵ (α , refl , refl) g f = refl
```
