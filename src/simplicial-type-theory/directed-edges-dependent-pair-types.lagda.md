# Directed edges in dependent pair types

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.directed-edges-dependent-pair-types
  {lI : Level} (I : Nontrivial-Bounded-Total-Order lI lI)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-maps

open import simplicial-type-theory.action-on-directed-edges-dependent-functions I
open import simplicial-type-theory.action-on-directed-edges-functions I
open import simplicial-type-theory.arrows I
open import simplicial-type-theory.dependent-directed-edges I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval-type I
```

</details>

## Idea

A [directed edge](simplicial-type-theory.directed-edges.md)
`f : (x , x') →▵ (y , y')` in a
[dependent pair type](foundation.dependent-pair-types.md) `Σ A B` consists of a
directed edge `α : x →▵ y` in the base `A` and a
[dependent directed edge](simplicial-type-theory.dependent-directed-edges.md)
`β` in `B` over `α` from `x'` to `y'`.

## Properties

### Characterizing directed edges in dependent pair types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  hom▵-Σ : (x y : Σ A B) → UU (lI ⊔ l1 ⊔ l2)
  hom▵-Σ (x , x') (y , y') =
    Σ (x →▵ y) (λ α → dependent-hom▵ B α x' y')

  action-hom▵-dependent-function-pr2' :
    {x y : Σ A B} (α : x →▵ y) →
    dependent-hom▵ B
      ( action-hom▵-function pr1 α)
      ( pr2 x)
      ( pr2 y)
  pr1 (action-hom▵-dependent-function-pr2' (α , p , q)) = pr2 ∘ α
  pr1 (pr2 (action-hom▵-dependent-function-pr2' (α , refl , q))) =
    refl
  pr2 (pr2 (action-hom▵-dependent-function-pr2' (α , p , refl))) =
    refl

  map-compute-hom▵-Σ :
    {x y : Σ A B} → x →▵ y → hom▵-Σ x y
  map-compute-hom▵-Σ α =
    ( action-hom▵-function pr1 α ,
      action-hom▵-dependent-function-pr2' α)

  map-inv-compute-hom▵-Σ :
    {x y : Σ A B} → hom▵-Σ x y → x →▵ y
  map-inv-compute-hom▵-Σ ((α , p , q) , (β , p' , q')) =
    ((λ t → (α t , β t)) , eq-pair-Σ p p' , eq-pair-Σ q q')

  is-section-map-inv-compute-hom▵-Σ :
    {x y : Σ A B} →
    is-section
      ( map-compute-hom▵-Σ {x} {y})
      ( map-inv-compute-hom▵-Σ)
  is-section-map-inv-compute-hom▵-Σ
    ( (α , refl , refl) , (β , refl , refl)) =
    refl

  is-retraction-map-inv-compute-hom▵-Σ :
    {x y : Σ A B} →
    is-retraction
      ( map-compute-hom▵-Σ {x} {y})
      ( map-inv-compute-hom▵-Σ)
  is-retraction-map-inv-compute-hom▵-Σ (α , refl , refl) = refl

  is-equiv-map-compute-hom▵-Σ :
    {x y : Σ A B} → is-equiv (map-compute-hom▵-Σ {x} {y})
  is-equiv-map-compute-hom▵-Σ =
    is-equiv-is-invertible
      ( map-inv-compute-hom▵-Σ)
      ( is-section-map-inv-compute-hom▵-Σ)
      ( is-retraction-map-inv-compute-hom▵-Σ)

  compute-hom▵-Σ : {x y : Σ A B} → (x →▵ y) ≃ hom▵-Σ x y
  compute-hom▵-Σ =
    ( map-compute-hom▵-Σ , is-equiv-map-compute-hom▵-Σ)

  inv-compute-hom▵-Σ :
    {x y : Σ A B} → hom▵-Σ x y ≃ (x →▵ y)
  inv-compute-hom▵-Σ = inv-equiv compute-hom▵-Σ
```
