# Horizontal composition of natural transformations between functions

```agda
module simplicial-type-theory.horizontal-composition-natural-transformations where
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
open import simplicial-type-theory.natural-transformations
open import simplicial-type-theory.horizontal-composition-directed-edges-functions
open import simplicial-type-theory.horizontal-composition-simplicial-arrows-functions
open import simplicial-type-theory.simplicial-arrows
```

</details>

## Idea

Given a natural transformation `α` between functions `f g : A → B` and a natural
transformation `β` of functions `f' g' : B → C`, we may
{{#concept "horizontally compose" Disambiguation="natural transformations of functions" Agda=horizontal-comp-simplicial-natural-transformation}}
them to obtain a natural transformation of functions `f' ∘ f ⇒▵ g' ∘ g`. The
horizontal composite is constructed by "synchronously traversing `α` and `β`",
defined on the underlying
[simplicial arrows](simplicial-type-theory.simplicial-arrows.md) as:

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

  horizontal-comp-simplicial-natural-transformation :
    f' ⇒▵ g' → f ⇒▵ g → (f' ∘ f) ⇒▵ (g' ∘ g)
  horizontal-comp-simplicial-natural-transformation β α x =
    ( λ t →
      simplicial-arrow-simplicial-hom
        ( β (simplicial-arrow-simplicial-hom (α x) t))
        ( t)) ,
    ( ( ap
        ( λ u → simplicial-arrow-simplicial-hom (β u) 0₂)
        ( eq-source-simplicial-natural-transformation α x)) ∙
      ( eq-source-simplicial-natural-transformation β (f x))) ,
    ( ( ap
        ( λ u → simplicial-arrow-simplicial-hom (β u) 1₂)
        ( eq-target-simplicial-natural-transformation α x)) ∙
      ( eq-target-simplicial-natural-transformation β (g x)))
```

### The action of a natural transformation on a directed edge

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B}
  where

  action-simplicial-hom-simplicial-natural-transformation :
    f ⇒▵ g → {x y : A} → x →₂ y → f x →₂ g y
  action-simplicial-hom-simplicial-natural-transformation α a =
    ( λ t →
      family-of-simplicial-arrows-simplicial-natural-transformation α
        ( simplicial-arrow-simplicial-hom a t)
        ( t)) ,
    ( ( eq-source-simplicial-natural-transformation α
        ( simplicial-arrow-simplicial-hom a 0₂)) ∙
      ( ap f (eq-source-simplicial-hom a))) ,
    ( ( eq-target-simplicial-natural-transformation α
        ( simplicial-arrow-simplicial-hom a 1₂)) ∙
      ( ap g (eq-target-simplicial-hom a)))
```

## Properties

### Unit laws for horizontal composition of directed edges of functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B}
  where

  left-unit-law-horizontal-comp-simplicial-natural-transformation :
    (α : f ⇒▵ g) →
    ( horizontal-comp-simplicial-natural-transformation
      ( id-simplicial-natural-transformation id)
      ( α)) ＝
    ( α)
  left-unit-law-horizontal-comp-simplicial-natural-transformation α =
    eq-htpy
      ( λ x →
        eq-pair-eq-fiber
          ( eq-pair
            ( right-unit ∙
              ap-id (eq-source-simplicial-natural-transformation α x))
            ( right-unit ∙
              ap-id (eq-target-simplicial-natural-transformation α x))))

  right-unit-law-horizontal-comp-simplicial-natural-transformation :
    (α : f ⇒▵ g) →
    ( horizontal-comp-simplicial-natural-transformation
      ( α)
      ( id-simplicial-natural-transformation id)) ＝
    ( α)
  right-unit-law-horizontal-comp-simplicial-natural-transformation α = refl
```

### Associativity of horizontal composition of directed edges of functions

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {h h' : C → D} {g g' : B → C} {f f' : A → B}
  where

  associative-horizontal-comp-simplicial-natural-transformation :
    (γ : h ⇒▵ h') (β : g ⇒▵ g') (α : f ⇒▵ f') →
    ( horizontal-comp-simplicial-natural-transformation
      ( horizontal-comp-simplicial-natural-transformation γ β)
      ( α)) ＝
    ( horizontal-comp-simplicial-natural-transformation
      ( γ)
      ( horizontal-comp-simplicial-natural-transformation β α))
  associative-horizontal-comp-simplicial-natural-transformation γ β α =
    eq-htpy
      ( λ x →
        eq-pair-eq-fiber
          ( eq-pair
            ( equational-reasoning {!  !} ＝ {!   !} by {!   !})
            {!   !}))
```
