# Horizontal composition of natural transformations between functions

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.horizontal-composition-natural-transformations
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
open import simplicial-type-theory.directed-interval-type I
open import simplicial-type-theory.horizontal-composition-arrows-functions I
open import simplicial-type-theory.horizontal-composition-directed-edges-functions I
open import simplicial-type-theory.natural-transformations I
```

</details>

## Idea

Given a
[natural transformation](simplicial-type-theory.natural-transformations.md) `α`
between functions `f g : A → B` and a natural transformation `β` of functions
`f' g' : B → C`, we may
{{#concept "horizontally compose" Disambiguation="natural transformations of functions" Agda=horizontal-comp-natural-transformation▵}}
them to obtain a natural transformation of functions `f' ∘ f ⇒▵ g' ∘ g`. The
horizontal composite is constructed by "synchronously traversing `α` and `β`",
defined on the underlying [simplicial arrows](simplicial-type-theory.arrows.md)
as:

```text
  β □ α := (t ↦ x ↦ β t (α t x)).
```

## Definitions

### Horizontal composition of natural transformations between functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B} {f' g' : B → C}
  where

  horizontal-comp-natural-transformation▵ :
    (f' ⇒▵ g') → (f ⇒▵ g) → ((f' ∘ f) ⇒▵ (g' ∘ g))
  horizontal-comp-natural-transformation▵ β α x =
    ( λ t → arrow-hom▵ (β (arrow-hom▵ (α x) t)) t) ,
    ( ( ap
        ( λ u → arrow-hom▵ (β u) 0▵)
        ( eq-source-natural-transformation▵ α x)) ∙
      ( eq-source-natural-transformation▵ β (f x))) ,
    ( ( ap
        ( λ u → arrow-hom▵ (β u) 1▵)
        ( eq-target-natural-transformation▵ α x)) ∙
      ( eq-target-natural-transformation▵ β (g x)))
```

### The action of a natural transformation on a directed edge

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B}
  where

  action-hom▵-natural-transformation▵ :
    (f ⇒▵ g) → {x y : A} → (x →▵ y) → (f x →▵ g y)
  action-hom▵-natural-transformation▵ α a =
    ( λ t →
      family-of-arrows-natural-transformation▵ α
        ( arrow-hom▵ a t)
        ( t)) ,
    ( ( eq-source-natural-transformation▵ α (arrow-hom▵ a 0▵)) ∙
      ( ap f (eq-source-hom▵ a))) ,
    ( ( eq-target-natural-transformation▵ α (arrow-hom▵ a 1▵)) ∙
      ( ap g (eq-target-hom▵ a)))
```

## Properties

### Unit laws for horizontal composition of directed edges of functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B}
  where

  left-unit-law-horizontal-comp-natural-transformation▵ :
    (α : f ⇒▵ g) →
    ( horizontal-comp-natural-transformation▵
      ( id-natural-transformation▵ id)
      ( α)) ＝
    ( α)
  left-unit-law-horizontal-comp-natural-transformation▵ α =
    eq-htpy
      ( λ x →
        eq-pair-eq-fiber
          ( eq-pair
            ( right-unit ∙
              ap-id (eq-source-natural-transformation▵ α x))
            ( right-unit ∙
              ap-id (eq-target-natural-transformation▵ α x))))

  right-unit-law-horizontal-comp-natural-transformation▵ :
    (α : f ⇒▵ g) →
    ( horizontal-comp-natural-transformation▵
      ( α)
      ( id-natural-transformation▵ id)) ＝
    ( α)
  right-unit-law-horizontal-comp-natural-transformation▵ α = refl
```

### Associativity of horizontal composition of directed edges of functions

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {h h' : C → D} {g g' : B → C} {f f' : A → B}
  where

  associative-horizontal-comp-natural-transformation▵ :
    (γ : h ⇒▵ h') (β : g ⇒▵ g') (α : f ⇒▵ f') →
    ( horizontal-comp-natural-transformation▵
      ( horizontal-comp-natural-transformation▵ γ β)
      ( α)) ＝
    ( horizontal-comp-natural-transformation▵
      ( γ)
      ( horizontal-comp-natural-transformation▵ β α))
  associative-horizontal-comp-natural-transformation▵ γ β α =
    eq-htpy
      ( λ x →
        eq-pair-eq-fiber
          ( eq-pair
            ( equational-reasoning {!  !} ＝ {!   !} by {!   !})
            {!   !}))
```
