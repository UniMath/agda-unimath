# The universal property of fiber products

```agda
open import foundation.function-extensionality-axiom

module foundation.universal-property-fiber-products
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams funext
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.standard-pullbacks funext
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks funext
open import foundation-core.universal-property-pullbacks funext
```

</details>

## Idea

The {{#concept "fiberwise product" Disambiguation="types"}} of two families `P`
and `Q` over a type `X` is the family of types `(P x) × (Q x)` over `X`.
Similarly, the fiber product of two maps `f : A → X` and `g : B → X` is the type
`Σ X (λ x → fiber f x × fiber g x)`, which fits in a
[pullback](foundation-core.pullbacks.md) diagram on `f` and `g`.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2) (Q : X → UU l3)
  where

  cone-fiberwise-product :
    cone (pr1 {B = P}) (pr1 {B = Q}) (Σ X (λ x → (P x) × (Q x)))
  pr1 cone-fiberwise-product = tot (λ _ → pr1)
  pr1 (pr2 cone-fiberwise-product) = tot (λ _ → pr2)
  pr2 (pr2 cone-fiberwise-product) = refl-htpy
```

We will show that the fiberwise product is a pullback by showing that the gap
map is an equivalence. We do this by directly construct an inverse to the gap
map.

```agda
  gap-fiberwise-product :
    Σ X (λ x → (P x) × (Q x)) → standard-pullback (pr1 {B = P}) (pr1 {B = Q})
  gap-fiberwise-product = gap pr1 pr1 cone-fiberwise-product

  inv-gap-fiberwise-product :
    standard-pullback (pr1 {B = P}) (pr1 {B = Q}) → Σ X (λ x → (P x) × (Q x))
  pr1 (inv-gap-fiberwise-product ((x , p) , (.x , q) , refl)) = x
  pr1 (pr2 (inv-gap-fiberwise-product ((x , p) , (.x , q) , refl))) = p
  pr2 (pr2 (inv-gap-fiberwise-product ((x , p) , (.x , q) , refl))) = q

  abstract
    is-section-inv-gap-fiberwise-product :
      (gap-fiberwise-product ∘ inv-gap-fiberwise-product) ~ id
    is-section-inv-gap-fiberwise-product ((x , p) , (.x , q) , refl) = refl

  abstract
    is-retraction-inv-gap-fiberwise-product :
      (inv-gap-fiberwise-product ∘ gap-fiberwise-product) ~ id
    is-retraction-inv-gap-fiberwise-product (x , p , q) = refl

  abstract
    is-pullback-fiberwise-product :
      is-pullback (pr1 {B = P}) (pr1 {B = Q}) cone-fiberwise-product
    is-pullback-fiberwise-product =
      is-equiv-is-invertible
        inv-gap-fiberwise-product
        is-section-inv-gap-fiberwise-product
        is-retraction-inv-gap-fiberwise-product

  abstract
    universal-property-pullback-fiberwise-product :
      universal-property-pullback
        ( pr1 {B = P})
        ( pr1 {B = Q})
        ( cone-fiberwise-product)
    universal-property-pullback-fiberwise-product =
      universal-property-pullback-is-pullback pr1 pr1
        cone-fiberwise-product
        is-pullback-fiberwise-product

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  cone-total-product-fibers : cone f g (Σ X (λ x → (fiber f x) × (fiber g x)))
  pr1 cone-total-product-fibers (x , (a , p) , (b , q)) = a
  pr1 (pr2 cone-total-product-fibers) (x , (a , p) , (b , q)) = b
  pr2 (pr2 cone-total-product-fibers) (x , (a , p) , (b , q)) = p ∙ inv q

  gap-total-product-fibers :
    Σ X (λ x → (fiber f x) × (fiber g x)) → standard-pullback f g
  gap-total-product-fibers = gap f g cone-total-product-fibers

  inv-gap-total-product-fibers :
    standard-pullback f g → Σ X (λ x → (fiber f x) × (fiber g x))
  pr1 (inv-gap-total-product-fibers (a , b , p)) = g b
  pr1 (pr1 (pr2 (inv-gap-total-product-fibers (a , b , p)))) = a
  pr2 (pr1 (pr2 (inv-gap-total-product-fibers (a , b , p)))) = p
  pr1 (pr2 (pr2 (inv-gap-total-product-fibers (a , b , p)))) = b
  pr2 (pr2 (pr2 (inv-gap-total-product-fibers (a , b , p)))) = refl

  abstract
    is-section-inv-gap-total-product-fibers :
      (gap-total-product-fibers ∘ inv-gap-total-product-fibers) ~ id
    is-section-inv-gap-total-product-fibers (a , b , p) =
      eq-Eq-standard-pullback f g refl refl
        ( inv right-unit ∙ inv right-unit)

  abstract
    is-retraction-inv-gap-total-product-fibers :
      (inv-gap-total-product-fibers ∘ gap-total-product-fibers) ~ id
    is-retraction-inv-gap-total-product-fibers (.(g b) , (a , p) , (b , refl)) =
      eq-pair-eq-fiber (eq-pair (eq-pair-eq-fiber right-unit) refl)

  abstract
    is-pullback-total-product-fibers :
      is-pullback f g cone-total-product-fibers
    is-pullback-total-product-fibers =
      is-equiv-is-invertible
        inv-gap-total-product-fibers
        is-section-inv-gap-total-product-fibers
        is-retraction-inv-gap-total-product-fibers
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
