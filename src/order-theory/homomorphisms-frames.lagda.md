# Title: Homomorphisms Frames 

```agda

module order-theory.homomorphisms-frames where

open import foundation.functions
open import foundation.cartesian-product-types 
open import foundation.dependent-pair-types 
open import foundation.propositions 
open import foundation.subtypes 
open import foundation.universe-levels
open import foundation.identity-types
open import foundation.sets

open import order-theory.posets
open import order-theory.least-upper-bounds-posets
open import order-theory.greatest-lower-bounds-posets
open import order-theory.sup-lattices
open import order-theory.meet-semilattices
open import order-theory.infinite-distributive-law
open import order-theory.order-preserving-maps-posets
open import order-theory.frames

```

## Idea
A frame homomorphism is an order preserving map between posets that additionally preserves binary meets and arbitrary joins.
*The longterm goal is to develop Homomorphisms of the preceeding structures (Meet-Semilattices and Sup Lattices) then we will
reformulate the following definitions. For now this is functional.*

```agda

module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : Frame l1 l2 l3) (B : Frame l4 l5 l6) 
  where
  
  preserves-meets : (element-Frame A → element-Frame B) → UU (l1 ⊔ l4 ⊔ l5)
  preserves-meets f = (x y : element-Frame A) → is-greatest-binary-lower-bound-Poset (poset-Frame B) (f x) (f y) (f (meet-Frame A x y))

  preserves-sups : (element-Frame A → element-Frame B) → UU (l1 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  preserves-sups f = {I : UU l3} → (b : I → element-Frame A) → is-least-upper-bound-family-Poset (poset-Frame B) (f ∘ b) (f (sup-Frame A I b)) 

  hom-Frame : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  hom-Frame = Σ (element-Frame A → element-Frame B)
    (λ f → preserves-order-Poset (poset-Frame A) (poset-Frame B) f × (preserves-meets f × preserves-sups f))

  map-hom-Frame : hom-Frame → element-Frame A → element-Frame B
  map-hom-Frame H = pr1 H

  preserves-order-Frame : (H : hom-Frame) → preserves-order-Poset (poset-Frame A) (poset-Frame B) (map-hom-Frame H)
  preserves-order-Frame H = pr1 (pr2 H)

  preserves-meet-Frame : (H : hom-Frame) → preserves-meets (map-hom-Frame H)
  preserves-meet-Frame H = pr1 (pr2 (pr2 H))

  preserves-sup-Frame : (H : hom-Frame) → preserves-sups (map-hom-Frame H)
  preserves-sup-Frame H = pr2 (pr2 (pr2 H))

```
