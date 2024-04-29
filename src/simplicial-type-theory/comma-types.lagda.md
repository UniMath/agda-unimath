# Comma types

```agda
module simplicial-type-theory.comma-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.directed-edges
```

</details>

## Idea

<!-- TODO -->

## Definitions

### The standard simplicial comma type

```agda
simplicial-comma-type :
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} →
  (B → A) → (C → A) → UU (l1 ⊔ l2 ⊔ l3)
simplicial-comma-type {B = B} {C} f g =
  Σ B (λ b → Σ C (λ c → simplicial-hom (f b) (g c)))

_↓₂_ = simplicial-comma-type
```

## Properties

### The universal property of the simplicial comma type

The comma type `f ↓₂ g` fits in a pullback diagram

```text
  f ↓₂ g --------> A^𝟚
    | ⌟             |
    |               | (source , target)
    ∨               ∨
  B × C --------> A × A
          f × g
```

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B → A) (g : C → A)
  where

  cone-simplicial-comma-type :
    cone
      {A = B × C} {𝟚 → A} {A × A}
      ( λ (b , c) → (f b , g c))
      ( λ α → (α 0₂ , α 1₂))
      ( f ↓₂ g)
  pr1 (cone-simplicial-comma-type) (b , c , _) = (b , c)
  pr1 (pr2 (cone-simplicial-comma-type)) (_ , _ , α , _) = α
  pr2 (pr2 (cone-simplicial-comma-type)) (_ , _ , _ , α0＝fb , α1＝gc) =
    inv (eq-pair α0＝fb α1＝gc)

  gap-simplicial-comma-type :
    f ↓₂ g → standard-pullback (λ (b , c) → (f b , g c)) (λ α → α 0₂ , α 1₂)
  gap-simplicial-comma-type =
    gap
      ( λ (b , c) → (f b , g c))
      ( λ α → (α 0₂ , α 1₂))
      ( cone-simplicial-comma-type)

  map-inv-gap-simplicial-comma-type :
    ( standard-pullback
      {A = B × C} {𝟚 → A} {A × A}
      ( λ (b , c) → (f b , g c))
      ( λ α → α 0₂ , α 1₂)) →
    f ↓₂ g
  map-inv-gap-simplicial-comma-type ((b , c) , α , coh) =
    ( b , c , α , pair-eq (inv coh))

  is-section-gap-simplicial-comma-type :
    map-inv-gap-simplicial-comma-type ∘ gap-simplicial-comma-type ~ id
  is-section-gap-simplicial-comma-type (b , c , α , coh) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( eq-pair-eq-fiber
          ( ap pair-eq (inv-inv (eq-pair' coh)) ∙ is-retraction-pair-eq coh)))

  is-retraction-gap-simplicial-comma-type :
    gap-simplicial-comma-type ∘ map-inv-gap-simplicial-comma-type ~ id
  is-retraction-gap-simplicial-comma-type ((b , c) , α , coh) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( ap inv (is-section-pair-eq (inv coh)) ∙ inv-inv coh))

  is-pullback-simplicial-comma-type :
    is-pullback
      ( λ (b , c) → (f b , g c))
      ( λ α → (α 0₂ , α 1₂))
      ( cone-simplicial-comma-type)
  is-pullback-simplicial-comma-type =
    is-equiv-is-invertible
      ( map-inv-gap-simplicial-comma-type)
      ( is-retraction-gap-simplicial-comma-type)
      ( is-section-gap-simplicial-comma-type)
```
