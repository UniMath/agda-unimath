# Directed edges in dependent pair types

```agda
module simplicial-type-theory.directed-edges-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.action-on-identifications-dependent-functions
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.sections
open import foundation.retractions
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-of-maps

open import simplicial-type-theory.action-on-directed-edges-functions
open import simplicial-type-theory.action-on-directed-edges-dependent-functions
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.dependent-simplicial-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
```

</details>

## Idea

A [directed edge](simplicial-type-theory.directed-edges.md)
`f : (x , x') →₂ (y , y')` in a
[dependent pair type](foundation.dependent-pair-types.md) `Σ A B` consists of a
directed edge `α : x →₂ y` in the base `A` and a
[dependent directed edge](simplicial-type-theory.dependent-simplicial-edges.md)
`β` in `B` over `α` from `x'` to `y'`.

## Properties

### Characterizing directed edges in dependent pair types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  simplicial-hom-Σ : (x y : Σ A B) → UU (l1 ⊔ l2)
  simplicial-hom-Σ (x , x') (y , y') =
    Σ (x →₂ y) (λ α → dependent-simplicial-hom B α x' y')

  action-simplicial-hom-dependent-function-pr2' :
    {x y : Σ A B} (α : x →₂ y) →
    dependent-simplicial-hom B
      ( action-simplicial-hom-function pr1 α)
      ( pr2 x)
      ( pr2 y)
  pr1 (action-simplicial-hom-dependent-function-pr2' (α , p , q)) = pr2 ∘ α
  pr1 (pr2 (action-simplicial-hom-dependent-function-pr2' (α , refl , q))) =
    refl
  pr2 (pr2 (action-simplicial-hom-dependent-function-pr2' (α , p , refl))) =
    refl

  map-compute-simplicial-hom-Σ :
    {x y : Σ A B} → x →₂ y → simplicial-hom-Σ x y
  map-compute-simplicial-hom-Σ α =
    ( action-simplicial-hom-function pr1 α ,
      action-simplicial-hom-dependent-function-pr2' α)

  map-inv-compute-simplicial-hom-Σ :
    {x y : Σ A B} → simplicial-hom-Σ x y → x →₂ y
  map-inv-compute-simplicial-hom-Σ ((α , p , q) , (β , p' , q')) =
    ((λ t → (α t , β t)) , eq-pair-Σ p p' , eq-pair-Σ q q')

  is-section-map-inv-compute-simplicial-hom-Σ :
    {x y : Σ A B} →
    is-section
      ( map-compute-simplicial-hom-Σ {x} {y})
      ( map-inv-compute-simplicial-hom-Σ)
  is-section-map-inv-compute-simplicial-hom-Σ
    ( (α , refl , refl) , (β , refl , refl)) =
    refl

  is-retraction-map-inv-compute-simplicial-hom-Σ :
    {x y : Σ A B} →
    is-retraction
      ( map-compute-simplicial-hom-Σ {x} {y})
      ( map-inv-compute-simplicial-hom-Σ)
  is-retraction-map-inv-compute-simplicial-hom-Σ (α , refl , refl) = refl

  is-equiv-map-compute-simplicial-hom-Σ :
    {x y : Σ A B} → is-equiv (map-compute-simplicial-hom-Σ {x} {y})
  is-equiv-map-compute-simplicial-hom-Σ =
    is-equiv-is-invertible
      ( map-inv-compute-simplicial-hom-Σ)
      ( is-section-map-inv-compute-simplicial-hom-Σ)
      ( is-retraction-map-inv-compute-simplicial-hom-Σ)

  compute-simplicial-hom-Σ : {x y : Σ A B} → (x →₂ y) ≃ simplicial-hom-Σ x y
  compute-simplicial-hom-Σ =
    ( map-compute-simplicial-hom-Σ , is-equiv-map-compute-simplicial-hom-Σ)

  inv-compute-simplicial-hom-Σ :
    {x y : Σ A B} → simplicial-hom-Σ x y ≃ (x →₂ y)
  inv-compute-simplicial-hom-Σ = inv-equiv compute-simplicial-hom-Σ
```
