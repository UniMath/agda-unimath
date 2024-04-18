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
open import simplicial-type-theory.simplicial-edges
```

</details>

## Idea

TODO

## Definition

```agda
simplicial-comma :
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} →
  (B → A) → (C → A) → UU (l1 ⊔ l2 ⊔ l3)
simplicial-comma {B = B} {C} f g =
  Σ B (λ b → Σ C (λ c → simplicial-hom (f b) (g c)))

_↓_ = simplicial-comma
```

## Properties

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B → A) (g : C → A)
  where

  cone-simplicial-comma :
    cone
      {A = B × C} {simplicial-arrow A} {A × A}
      ( λ (b , c) → (f b , g c))
      ( λ α → (α 0₂ , α 1₂))
      ( f ↓ g)
  pr1 (cone-simplicial-comma) (b , c , _) = (b , c)
  pr1 (pr2 (cone-simplicial-comma)) (_ , _ , α , _) = α
  pr2 (pr2 (cone-simplicial-comma)) (_ , _ , _ , α0＝fb , α1＝gc) =
    inv (eq-pair α0＝fb α1＝gc)

  gap-simplicial-comma :
    f ↓ g → standard-pullback (λ (b , c) → (f b , g c)) (λ α → α 0₂ , α 1₂)
  gap-simplicial-comma =
    gap (λ (b , c) → (f b , g c)) (λ α → (α 0₂ , α 1₂)) cone-simplicial-comma

  map-inv-gap-simplicial-comma :
    ( standard-pullback
      { A = B × C} {simplicial-arrow A} {A × A}
      ( λ (b , c) → (f b , g c))
      ( λ α → α 0₂ , α 1₂)) →
    f ↓ g
  map-inv-gap-simplicial-comma ((b , c) , α , coh) =
    b , c , α , pair-eq (inv coh)

  is-section-gap-simplicial-comma :
    map-inv-gap-simplicial-comma ∘ gap-simplicial-comma ~ id
  is-section-gap-simplicial-comma (b , c , α , coh) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( eq-pair-eq-fiber
          ( ap pair-eq (inv-inv (eq-pair' coh)) ∙ is-retraction-pair-eq coh)))

  is-retraction-gap-simplicial-comma :
    gap-simplicial-comma ∘ map-inv-gap-simplicial-comma ~ id
  is-retraction-gap-simplicial-comma ((b , c) , α , coh) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( ap inv (is-section-pair-eq (inv coh)) ∙ inv-inv coh))

  is-pullback-simplicial-comma :
    is-pullback
      ( λ (b , c) → (f b , g c))
      ( λ α → (α 0₂ , α 1₂))
      ( cone-simplicial-comma)
  is-pullback-simplicial-comma =
    is-equiv-is-invertible
      ( map-inv-gap-simplicial-comma)
      ( is-retraction-gap-simplicial-comma)
      ( is-section-gap-simplicial-comma)
```
