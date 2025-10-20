# Horizontal composition of directed edges between functions

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.horizontal-composition-directed-edges-functions
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
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

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.horizontal-composition-arrows-functions I
```

</details>

## Idea

Given a directed edge `α` between functions `f g : A → B` and a directed edge
`β` of functions `f' g' : B → C`, we may
{{#concept "horizontally compose" Disambiguation="directed edges of functions" Agda=horizontal-comp-hom▵}}
them to obtain a directed edge of functions `f' ∘ f →▵ g' ∘ g`. The horizontal
composite is constructed by "synchronously traversing `α` and `β`", defined on
the underlying [arrows](simplicial-type-theory.arrows.md) as:

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

  horizontal-comp-hom▵ : f' →▵ g' → f →▵ g → (f' ∘ f) →▵ (g' ∘ g)
  horizontal-comp-hom▵ (β , s , t) (α , s' , t') =
    ( ( horizontal-comp-arrow▵ β α) ,
      ( ap (β 0▵ ∘_) s' ∙ ap (_∘ f) s) ,
      ( ap (β 1▵ ∘_) t' ∙ ap (_∘ g) t))
```

## Properties

### Unit laws for horizontal composition of directed edges of functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B}
  where

  left-unit-law-horizontal-comp-hom▵ :
    (α : f →▵ g) →
    horizontal-comp-hom▵ (id-hom▵ id) α ＝ α
  left-unit-law-horizontal-comp-hom▵ (α , s , t) =
    eq-pair-eq-fiber (eq-pair (right-unit ∙ ap-id s) (right-unit ∙ ap-id t))

  right-unit-law-horizontal-comp-hom▵ :
    (α : f →▵ g) →
    horizontal-comp-hom▵ α (id-hom▵ id) ＝ α
  right-unit-law-horizontal-comp-hom▵ (α , s , t) =
    eq-pair-eq-fiber (eq-pair (ap-id s) (ap-id t))
```

### Associativity of horizontal composition of directed edges of functions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {h h' : C → D} {g g' : B → C} {f f' : A → B}
  where

  associative-horizontal-comp-hom▵ :
    (γ : h →▵ h') (β : g →▵ g') (α : f →▵ f') →
    horizontal-comp-hom▵ (horizontal-comp-hom▵ γ β) α ＝
    horizontal-comp-hom▵ γ (horizontal-comp-hom▵ β α)
  associative-horizontal-comp-hom▵
    ( γ , refl , refl) (β , refl , refl) (α , refl , refl) = refl
```
