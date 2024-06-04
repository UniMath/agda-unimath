# Horizontal composition of directed edges between functions

```agda
module simplicial-type-theory.horizontal-composition-simplicial-edges-functions where
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

open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.horizontal-composition-simplicial-arrows-functions
open import simplicial-type-theory.simplicial-arrows
```

</details>

## Idea

Given a directed edge `α` between functions `f g : A → B` and a simplicial edge
`β` of functions `f' g' : B → C`, we may
{{#concept "horizontally compose" Disambiguation="directed edges of functions" Agda=horizontal-comp-simplicial-hom}}
them to obtain a directed edge of functions `f' ∘ f →₂ g' ∘ g`. The horizontal
composite is constructed by "synchronously traversing `α` and `β`", defined on
the underlying [simplicial arrows](simplicial-type-theory.simplicial-arrows.md)
as:

```text
  β □ α := (t ↦ x ↦ β t (α t x)).
```

## Definitions

### Horizontal composition of directed edges between functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B} {f' g' : B → C}
  where

  horizontal-comp-simplicial-hom : f' →₂ g' → f →₂ g → (f' ∘ f) →₂ (g' ∘ g)
  horizontal-comp-simplicial-hom (β , s , t) (α , s' , t') =
    ( ( horizontal-comp-simplicial-arrow β α) ,
      ( ap (β 0₂ ∘_) s' ∙ ap (_∘ f) s) ,
      ( ap (β 1₂ ∘_) t' ∙ ap (_∘ g) t))
```

## Properties

### Unit laws for horizontal composition of directed edges of functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B}
  where

  left-unit-law-horizontal-comp-simplicial-hom :
    (α : f →₂ g) →
    horizontal-comp-simplicial-hom (id-simplicial-hom id) α ＝ α
  left-unit-law-horizontal-comp-simplicial-hom (α , s , t) =
    eq-pair-eq-fiber (eq-pair (right-unit ∙ ap-id s) (right-unit ∙ ap-id t))

  right-unit-law-horizontal-comp-simplicial-hom :
    (α : f →₂ g) →
    horizontal-comp-simplicial-hom α (id-simplicial-hom id) ＝ α
  right-unit-law-horizontal-comp-simplicial-hom (α , s , t) =
    eq-pair-eq-fiber (eq-pair (ap-id s) (ap-id t))
```

### Associativity of horizontal composition of directed edges of functions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {h h' : C → D} {g g' : B → C} {f f' : A → B}
  where

  associative-horizontal-comp-simplicial-hom :
    (γ : h →₂ h') (β : g →₂ g') (α : f →₂ f') →
    horizontal-comp-simplicial-hom (horizontal-comp-simplicial-hom γ β) α ＝
    horizontal-comp-simplicial-hom γ (horizontal-comp-simplicial-hom β α)
  associative-horizontal-comp-simplicial-hom
    ( γ , refl , refl) (β , refl , refl) (α , refl , refl) = refl
```
