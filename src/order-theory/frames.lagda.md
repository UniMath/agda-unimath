# Title: Frames 

```agda

module order-theory.frames where

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

```

## Idea: A frame is a poset that has binary meets and arbitrary joins and further satisfies the infinite distributive law.
There are many equivalent ways to formulate this definition. Our choice here is simply motivated by a desire to avoid
iterated sigma types. 

```agda

Frame : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Frame l1 l2 l3 = Σ (Meet-Sup-Lattice l1 l2 l3) (distributive-law-meet-sup-lattice l1 l2 l3 ) 

```

## Now we retrieve all the information from a frame (i.e. break up all of it's components, etc.)


```agda

module _
  {l1 l2 l3 : Level} (A : Frame l1 l2 l3)
  where

  poset-Frame : Poset l1 l2
  poset-Frame = poset-Meet-Sup-Lattice (pr1 A)

  element-Frame : UU l1
  element-Frame = element-Poset poset-Frame

  leq-Frame-Prop : (x y : element-Frame) → Prop l2
  leq-Frame-Prop = leq-poset-Prop poset-Frame

  leq-Frame : (x y : element-Frame) → UU l2
  leq-Frame = leq-Poset poset-Frame

  is-prop-leq-Frame :
    (x y : element-Frame) → is-prop (leq-Frame x y)
  is-prop-leq-Frame = is-prop-leq-Poset poset-Frame
  refl-leq-Frame :
    (x : element-Frame) → leq-Frame x x
  refl-leq-Frame = refl-leq-Poset poset-Frame

  antisymmetric-leq-Frame :
    (x y : element-Frame) →
    leq-Frame x y → leq-Frame y x → x ＝ y
  antisymmetric-leq-Frame =
    antisymmetric-leq-Poset poset-Frame

  transitive-leq-Frame :
    (x y z : element-Frame) →
    leq-Frame y z → leq-Frame x y →
    leq-Frame x z
  transitive-leq-Frame = transitive-leq-Poset poset-Frame

  is-set-element-Frame : is-set element-Frame
  is-set-element-Frame = is-set-element-Poset poset-Frame

  element-frame-Set : Set l1
  element-frame-Set = element-poset-Set poset-Frame

  is-meet-semilattice-Frame :
    is-meet-semilattice-Poset poset-Frame
  is-meet-semilattice-Frame = is-meet-semilattice-Meet-Sup-Lattice (pr1 A)

  is-sup-lattice-Frame :
    is-sup-lattice-Poset l3 poset-Frame
  is-sup-lattice-Frame = is-sup-lattice-Meet-Sup-Lattice (pr1 A)

  meet-sup-lattice-Frame :
    Meet-Sup-Lattice l1 l2 l3
  pr1 meet-sup-lattice-Frame =
    poset-Frame
  pr1 (pr2 meet-sup-lattice-Frame) =
    is-meet-semilattice-Frame
  pr2 (pr2 meet-sup-lattice-Frame) =
    is-sup-lattice-Frame

  meet-Frame :
    (x y : element-Frame) →
    element-Frame
  meet-Frame x y = pr1 (is-meet-semilattice-Frame x y)

  sup-Frame :
    (I : UU l3) → (I → element-Frame) →
    element-Frame
  sup-Frame I b = pr1 (is-sup-lattice-Frame I b)

  distributive-law-Frame : distributive-law-meet-sup-lattice l1 l2 l3 meet-sup-lattice-Frame
  distributive-law-Frame = pr2 A

  frame-Frame : Frame l1 l2 l3
  pr1 frame-Frame = meet-sup-lattice-Frame
  pr2 frame-Frame = distributive-law-Frame

```

## Frame homomorphisms
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
