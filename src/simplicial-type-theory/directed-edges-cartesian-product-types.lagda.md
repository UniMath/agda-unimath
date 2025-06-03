# Directed edges in cartesian product types

```agda
module simplicial-type-theory.directed-edges-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
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

open import simplicial-type-theory.action-on-directed-edges-dependent-functions
open import simplicial-type-theory.action-on-directed-edges-functions
open import simplicial-type-theory.dependent-directed-edges
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
```

</details>

## Idea

A [directed edge](simplicial-type-theory.directed-edges.md)
`f : (x , x') →▵ (y , y')` in a
[cartesian product type](foundation.dependent-pair-types.md) `A × B` consists of
a directed edge `α : x →▵ y` in `A` and a directed edge `β : x' →▵ y'` in `B`.

## Properties

### Characterizing directed edges in cartesian product types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  hom▵-product : (x y : A × B) → UU (l1 ⊔ l2)
  hom▵-product (x , x') (y , y') = (x →▵ y) × (x' →▵ y')

  map-compute-hom▵-product :
    {x y : A × B} → x →▵ y → hom▵-product x y
  map-compute-hom▵-product α =
    ( action-hom▵-function pr1 α ,
      action-hom▵-function pr2 α)

  map-inv-compute-hom▵-product :
    {x y : A × B} → hom▵-product x y → x →▵ y
  map-inv-compute-hom▵-product ((α , p , q) , (β , p' , q')) =
    ((λ t → (α t , β t)) , eq-pair p p' , eq-pair q q')

  is-section-map-inv-compute-hom▵-product :
    {x y : A × B} →
    is-section
      ( map-compute-hom▵-product {x} {y})
      ( map-inv-compute-hom▵-product)
  is-section-map-inv-compute-hom▵-product
    ( ( α , refl , refl) , (β , refl , refl)) =
    refl

  is-retraction-map-inv-compute-hom▵-product :
    {x y : A × B} →
    is-retraction
      ( map-compute-hom▵-product {x} {y})
      ( map-inv-compute-hom▵-product)
  is-retraction-map-inv-compute-hom▵-product (α , refl , refl) = refl

  is-equiv-map-compute-hom▵-product :
    {x y : A × B} → is-equiv (map-compute-hom▵-product {x} {y})
  is-equiv-map-compute-hom▵-product =
    is-equiv-is-invertible
      ( map-inv-compute-hom▵-product)
      ( is-section-map-inv-compute-hom▵-product)
      ( is-retraction-map-inv-compute-hom▵-product)

  compute-hom▵-product :
    {x y : A × B} → (x →▵ y) ≃ hom▵-product x y
  compute-hom▵-product =
    ( map-compute-hom▵-product ,
      is-equiv-map-compute-hom▵-product)

  inv-compute-hom▵-product :
    {x y : A × B} → hom▵-product x y ≃ (x →▵ y)
  inv-compute-hom▵-product = inv-equiv compute-hom▵-product
```
