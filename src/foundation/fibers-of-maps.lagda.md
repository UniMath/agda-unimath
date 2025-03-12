# Fibers of maps

```agda
module foundation.fibers-of-maps where

open import foundation-core.fibers-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.postcomposition-functions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
open import foundation-core.transport-along-identifications
open import foundation-core.universal-property-pullbacks
```

</details>

## Properties

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  square-fiber :
    f ∘ pr1 ~ point b ∘ terminal-map (fiber f b)
  square-fiber = pr2

  cone-fiber : cone f (point b) (fiber f b)
  pr1 cone-fiber = pr1
  pr1 (pr2 cone-fiber) = terminal-map (fiber f b)
  pr2 (pr2 cone-fiber) = square-fiber

  abstract
    is-pullback-cone-fiber : is-pullback f (point b) cone-fiber
    is-pullback-cone-fiber =
      is-equiv-tot-is-fiberwise-equiv
        ( λ a → is-equiv-map-inv-left-unit-law-product)

  abstract
    universal-property-pullback-cone-fiber :
      universal-property-pullback f (point b) cone-fiber
    universal-property-pullback-cone-fiber =
      universal-property-pullback-is-pullback f
        ( point b)
        ( cone-fiber)
        ( is-pullback-cone-fiber)
```

### The fiber of the terminal map at any point is equivalent to its domain

```agda
module _
  {l : Level} {A : UU l}
  where

  equiv-fiber-terminal-map :
    (u : unit) → fiber (terminal-map A) u ≃ A
  equiv-fiber-terminal-map u =
    right-unit-law-Σ-is-contr
      ( λ a → is-prop-unit (terminal-map A a) u)

  inv-equiv-fiber-terminal-map :
    (u : unit) → A ≃ fiber (terminal-map A) u
  inv-equiv-fiber-terminal-map u =
    inv-equiv (equiv-fiber-terminal-map u)

  equiv-fiber-terminal-map-star :
    fiber (terminal-map A) star ≃ A
  equiv-fiber-terminal-map-star = equiv-fiber-terminal-map star

  inv-equiv-fiber-terminal-map-star :
    A ≃ fiber (terminal-map A) star
  inv-equiv-fiber-terminal-map-star =
    inv-equiv equiv-fiber-terminal-map-star
```

### The total space of the fibers of the terminal map is equivalent to its domain

```agda
module _
  {l : Level} {A : UU l}
  where

  equiv-total-fiber-terminal-map :
    Σ unit (fiber (terminal-map A)) ≃ A
  equiv-total-fiber-terminal-map =
    ( left-unit-law-Σ-is-contr is-contr-unit star) ∘e
    ( equiv-tot equiv-fiber-terminal-map)

  inv-equiv-total-fiber-terminal-map :
    A ≃ Σ unit (fiber (terminal-map A))
  inv-equiv-total-fiber-terminal-map =
    inv-equiv equiv-total-fiber-terminal-map
```

### Computing the fibers of postcomposition by a projection map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  compute-fiber-postcomp-pr1 :
    {l3 : Level} {X : UU l3} (h : X → A) →
    ((i : X) → B (h i)) ≃ fiber (postcomp X (pr1 {B = B})) h
  compute-fiber-postcomp-pr1 {X = X} h =
    compute-Π-fiber-postcomp X pr1 h ∘e
    equiv-Π-equiv-family (λ i → inv-equiv-fiber-pr1 B (h i))

  compute-fiber-id-postcomp-pr1 :
    ((a : A) → B a) ≃ fiber (postcomp A (pr1 {B = B})) id
  compute-fiber-id-postcomp-pr1 = compute-fiber-postcomp-pr1 id
```

### Transport in fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  compute-tr-fiber :
    {y y' : B} (p : y ＝ y') (u : fiber f y) →
    tot (λ x → concat' _ p) u ＝ tr (fiber f) p u
  compute-tr-fiber refl u = ap (pair _) right-unit

  inv-compute-tr-fiber :
    {y y' : B} (p : y ＝ y') (u : fiber f y) →
    tr (fiber f) p u ＝ tot (λ x → concat' _ p) u
  inv-compute-tr-fiber p u = inv (compute-tr-fiber p u)

  compute-tr-fiber' :
    {y y' : B} (p : y ＝ y') (u : fiber' f y) →
    tot (λ x q → inv p ∙ q) u ＝ tr (fiber' f) p u
  compute-tr-fiber' refl u = refl

  inv-compute-tr-fiber' :
    {y y' : B} (p : y ＝ y') (u : fiber' f y) →
    tr (fiber' f) p u ＝ tot (λ x q → inv p ∙ q) u
  inv-compute-tr-fiber' p u = inv (compute-tr-fiber' p u)
```

### Transport in fibers along the fiber

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  compute-tr-self-fiber :
    {y : B} (u : fiber f y) → (pr1 u , refl) ＝ tr (fiber f) (inv (pr2 u)) u
  compute-tr-self-fiber (._ , refl) = refl

  inv-compute-tr-self-fiber :
    {y : B} (u : fiber f y) → tr (fiber f) (inv (pr2 u)) u ＝ (pr1 u , refl)
  inv-compute-tr-self-fiber u = inv (compute-tr-self-fiber u)

  compute-tr-self-fiber' :
    {y : B} (u : fiber' f y) → (pr1 u , refl) ＝ tr (fiber' f) (pr2 u) u
  compute-tr-self-fiber' (._ , refl) = refl

  inv-compute-tr-self-fiber' :
    {y : B} (u : fiber' f y) → tr (fiber' f) (pr2 u) u ＝ (pr1 u , refl)
  inv-compute-tr-self-fiber' u = inv (compute-tr-self-fiber' u)
```

## Table of files about fibers of maps

The following table lists files that are about fibers of maps as a general
concept.

{{#include tables/fibers-of-maps.md}}
