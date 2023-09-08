# The universal property of fiber products

```agda
module foundation.universal-property-fiber-products where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

The fiberwise product of two families `P` and `Q` over a type `X` is the family
of types `(P x) × (Q x)` over `X`. Similarly, the fiber product of two maps
`f :A → X` and `g : B → X` is the type `Σ X (λ x → fiber f x × fiber g x)`,
which fits in a pullback diagram on `f` and `g`.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2) (Q : X → UU l3)
  where

  cone-fiberwise-prod :
    cone (pr1 {B = P}) (pr1 {B = Q}) (Σ X (λ x → (P x) × (Q x)))
  pr1 cone-fiberwise-prod = tot (λ x → pr1)
  pr1 (pr2 cone-fiberwise-prod) = tot (λ x → pr2)
  pr2 (pr2 cone-fiberwise-prod) = refl-htpy
```

We will show that the fiberwise product is a pullback by showing that the gap
map is an equivalence. We do this by directly construct an inverse to the gap
map.

```agda
  gap-fiberwise-prod :
    Σ X (λ x → (P x) × (Q x)) → canonical-pullback (pr1 {B = P}) (pr1 {B = Q})
  gap-fiberwise-prod = gap pr1 pr1 cone-fiberwise-prod

  inv-gap-fiberwise-prod :
    canonical-pullback (pr1 {B = P}) (pr1 {B = Q}) → Σ X (λ x → (P x) × (Q x))
  pr1 (inv-gap-fiberwise-prod ((x , p) , ((.x , q) , refl))) = x
  pr1 (pr2 (inv-gap-fiberwise-prod ((x , p) , ((.x , q) , refl)))) = p
  pr2 (pr2 (inv-gap-fiberwise-prod ((x , p) , ((.x , q) , refl)))) = q

  abstract
    is-section-inv-gap-fiberwise-prod :
      (gap-fiberwise-prod ∘ inv-gap-fiberwise-prod) ~ id
    is-section-inv-gap-fiberwise-prod ((x , p) , ((.x , q) , refl)) =
      eq-pair-Σ refl (eq-pair-Σ refl refl)

  abstract
    is-retraction-inv-gap-fiberwise-prod :
      (inv-gap-fiberwise-prod ∘ gap-fiberwise-prod) ~ id
    is-retraction-inv-gap-fiberwise-prod (x , p , q) = refl

  abstract
    is-pullback-fiberwise-prod :
      is-pullback (pr1 {B = P}) (pr1 {B = Q}) cone-fiberwise-prod
    is-pullback-fiberwise-prod =
      is-equiv-is-invertible
        inv-gap-fiberwise-prod
        is-section-inv-gap-fiberwise-prod
        is-retraction-inv-gap-fiberwise-prod

  abstract
    universal-property-pullback-fiberwise-prod :
      {l : Level} →
      universal-property-pullback l
        ( pr1 {B = P})
        ( pr1 {B = Q})
        ( cone-fiberwise-prod)
    universal-property-pullback-fiberwise-prod =
      universal-property-pullback-is-pullback pr1 pr1
        cone-fiberwise-prod
        is-pullback-fiberwise-prod

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  cone-total-prod-fibers : cone f g (Σ X (λ x → (fiber f x) × (fiber g x)))
  pr1 cone-total-prod-fibers (x , (a , p) , (b , q)) = a
  pr1 (pr2 cone-total-prod-fibers) (x , (a , p) , (b , q)) = b
  pr2 (pr2 cone-total-prod-fibers) (x , (a , p) , (b , q)) = p ∙ inv q

  gap-total-prod-fibers :
    Σ X (λ x → (fiber f x) × (fiber g x)) → canonical-pullback f g
  gap-total-prod-fibers = gap f g cone-total-prod-fibers

  inv-gap-total-prod-fibers :
    canonical-pullback f g → Σ X (λ x → (fiber f x) × (fiber g x))
  pr1 (inv-gap-total-prod-fibers (a , b , p)) = g b
  pr1 (pr1 (pr2 (inv-gap-total-prod-fibers (a , b , p)))) = a
  pr2 (pr1 (pr2 (inv-gap-total-prod-fibers (a , b , p)))) = p
  pr1 (pr2 (pr2 (inv-gap-total-prod-fibers (a , b , p)))) = b
  pr2 (pr2 (pr2 (inv-gap-total-prod-fibers (a , b , p)))) = refl

  abstract
    is-section-inv-gap-total-prod-fibers :
      (gap-total-prod-fibers ∘ inv-gap-total-prod-fibers) ~ id
    is-section-inv-gap-total-prod-fibers (a , b , p) =
      map-extensionality-canonical-pullback f g refl refl
        ( inv right-unit ∙ inv right-unit)

  abstract
    is-retraction-inv-gap-total-prod-fibers :
      (inv-gap-total-prod-fibers ∘ gap-total-prod-fibers) ~ id
    is-retraction-inv-gap-total-prod-fibers (.(g b) , (a , p) , (b , refl)) =
      eq-pair-Σ refl (eq-pair (eq-pair-Σ refl right-unit) refl)

  abstract
    is-pullback-total-prod-fibers :
      is-pullback f g cone-total-prod-fibers
    is-pullback-total-prod-fibers =
      is-equiv-is-invertible
        inv-gap-total-prod-fibers
        is-section-inv-gap-total-prod-fibers
        is-retraction-inv-gap-total-prod-fibers
```
