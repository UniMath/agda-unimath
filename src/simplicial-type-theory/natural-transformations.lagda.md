# Natural transformations

```agda
module simplicial-type-theory.natural-transformations where
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

open import simplicial-type-theory.action-on-directed-edges-functions
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
```

</details>

## Idea

Given two dependent functions `f g : (x : A) → B x`, a
{{#concept "simplicial natural transformation" Disambiguation="simplicial type theory" Agda=simplicial-natural-transformation}}
`α` from `f` to `g` is a family of directed edges

```text
  α : (x : A) → (f x →▵ g x).
```

Naturality follows automatically from the fact that every section is natural in
the base. I.e., for every edge `x →▵ y` in `A`, we have a dependent edge
`α x →▵ α y` over it, giving us a commuting dependent square of simplicial
arrows

```text
           α x
     f x ------> g x
      |           |
  f p |    α p    | g p
      ∨           ∨
     f y ------> g y.
           α y
```

## Definitions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _⇒▵_ : ((x : A) → B x) → ((x : A) → B x) → UU (l1 ⊔ l2)
  f ⇒▵ g = (x : A) → f x →▵ g x

  infix 7 _⇒▵_

  simplicial-natural-transformation :
    ((x : A) → B x) → ((x : A) → B x) → UU (l1 ⊔ l2)
  simplicial-natural-transformation = _⇒▵_

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} (α : f ⇒▵ g)
  where

  family-of-simplicial-arrows-simplicial-natural-transformation :
    (x : A) → arrow▵ (B x)
  family-of-simplicial-arrows-simplicial-natural-transformation x t =
    arrow-hom▵ (α x) t

  eq-source-simplicial-natural-transformation :
    (x : A) →
    family-of-simplicial-arrows-simplicial-natural-transformation x 0₂ ＝ f x
  eq-source-simplicial-natural-transformation x =
    eq-source-hom▵ (α x)

  eq-target-simplicial-natural-transformation :
    (x : A) →
    family-of-simplicial-arrows-simplicial-natural-transformation x 1₂ ＝ g x
  eq-target-simplicial-natural-transformation x =
    eq-target-hom▵ (α x)
```

## Properties

### Families of simplicial arrows are simplicial arrows of dependent functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → 𝟚 → UU l2}
  where

  family-of-simplicial-arrows-arrow▵-of-dependent-functions :
    arrow▵' (λ t → (x : A) → B x t) →
    (x : A) → arrow▵' (B x)
  family-of-simplicial-arrows-arrow▵-of-dependent-functions = swap-Π

  arrow▵-of-dependent-functions-family-of-simplicial-arrows :
    ((x : A) → arrow▵' (B x)) →
    arrow▵' (λ t → (x : A) → B x t)
  arrow▵-of-dependent-functions-family-of-simplicial-arrows = swap-Π

  equiv-family-of-simplicial-arrows-arrow▵-of-dependent-functions :
    ( arrow▵' (λ t → (x : A) → B x t)) ≃
    ( (x : A) → arrow▵' (B x))
  equiv-family-of-simplicial-arrows-arrow▵-of-dependent-functions =
    equiv-swap-Π
```

### Extensionality for simplicial natural transformations

A simplicial natural transformation between functions `f` and `g` is the same as
a directed edge from `f` to `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  simplicial-natural-transformation-simplicial-edge-of-dependent-functions :
    f →▵ g → f ⇒▵ g
  simplicial-natural-transformation-simplicial-edge-of-dependent-functions
    ( α , p , q) x =
    ( ( λ t → α t x) , htpy-eq p x , htpy-eq q x)

  simplicial-edge-of-dependent-functions-simplicial-natural-transformation :
    f ⇒▵ g → f →▵ g
  simplicial-edge-of-dependent-functions-simplicial-natural-transformation α =
    ( (λ t x → pr1 (α x) t) , eq-htpy (pr1 ∘ pr2 ∘ α) , eq-htpy (pr2 ∘ pr2 ∘ α))

  is-section-simplicial-edge-of-dependent-functions-simplicial-natural-transformation :
    is-section
      ( simplicial-natural-transformation-simplicial-edge-of-dependent-functions)
      ( simplicial-edge-of-dependent-functions-simplicial-natural-transformation)
  is-section-simplicial-edge-of-dependent-functions-simplicial-natural-transformation
    α =
    eq-htpy
      ( λ x →
        eq-pair-eq-fiber
          ( eq-pair
            ( htpy-eq (is-section-eq-htpy (pr1 ∘ pr2 ∘ α)) x)
            ( htpy-eq (is-section-eq-htpy (pr2 ∘ pr2 ∘ α)) x)))

  is-retraction-simplicial-edge-of-dependent-functions-simplicial-natural-transformation :
    is-retraction
      ( simplicial-natural-transformation-simplicial-edge-of-dependent-functions)
      ( simplicial-edge-of-dependent-functions-simplicial-natural-transformation)
  is-retraction-simplicial-edge-of-dependent-functions-simplicial-natural-transformation
    ( α , p , q) =
    eq-pair-eq-fiber
      ( eq-pair (is-retraction-eq-htpy p) (is-retraction-eq-htpy q))

  is-equiv-simplicial-natural-transformation-simplicial-edge-of-dependent-functions :
    is-equiv
      ( simplicial-natural-transformation-simplicial-edge-of-dependent-functions)
  is-equiv-simplicial-natural-transformation-simplicial-edge-of-dependent-functions =
    is-equiv-is-invertible
      ( simplicial-edge-of-dependent-functions-simplicial-natural-transformation)
      ( is-section-simplicial-edge-of-dependent-functions-simplicial-natural-transformation)
      ( is-retraction-simplicial-edge-of-dependent-functions-simplicial-natural-transformation)

  extensionality-simplicial-natural-transformation : (f →▵ g) ≃ (f ⇒▵ g)
  extensionality-simplicial-natural-transformation =
    ( simplicial-natural-transformation-simplicial-edge-of-dependent-functions ,
      is-equiv-simplicial-natural-transformation-simplicial-edge-of-dependent-functions)
```

## The identity natural transformation

```agda
id-simplicial-natural-transformation :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) → f ⇒▵ f
id-simplicial-natural-transformation f x = id-hom▵ (f x)
```
