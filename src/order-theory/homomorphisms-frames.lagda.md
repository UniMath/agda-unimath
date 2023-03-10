# Homomorphisms Frames

```agda
module order-theory.homomorphisms-frames where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.frames
open import order-theory.greatest-lower-bounds-posets
open import order-theory.homomorphisms-meet-semilattices
open import order-theory.homomorphisms-meet-sup-lattices
open import order-theory.homomorphisms-sup-lattices
open import order-theory.infinite-distributive-law
open import order-theory.least-upper-bounds-posets
open import order-theory.meet-semilattices
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.sup-lattices
```

</details>

## Idea
A frame homomorphism is an order preserving map between posets that additionally preserves binary meets and arbitrary joins.

```agda

module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : Frame l1 l2 l3) (B : Frame l4 l5 l6)
  where

  hom-Frame : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  hom-Frame = Σ (element-Frame A → element-Frame B)
    (λ f → preserves-order-Poset (poset-Frame A) (poset-Frame B) f ×
      preserves-meets-sups (meet-sup-lattice-Frame A) (meet-sup-lattice-Frame B) f)

  map-hom-Frame : hom-Frame → element-Frame A → element-Frame B
  map-hom-Frame = pr1

  preserves-order-hom-Frame : (H : hom-Frame) → preserves-order-Poset (poset-Frame A) (poset-Frame B) (map-hom-Frame H)
  preserves-order-hom-Frame = pr1 ∘ pr2

  preserves-meets-sups-hom-Frame : (H : hom-Frame) → preserves-meets-sups (meet-sup-lattice-Frame A) (meet-sup-lattice-Frame B) (map-hom-Frame H)
  preserves-meets-sups-hom-Frame = pr2 ∘ pr2

  preserves-meets-hom-Frame : (H : hom-Frame) → preserves-meets (meet-semilattice-Frame A) (meet-semilattice-Frame B) (map-hom-Frame H)
  preserves-meets-hom-Frame = pr1 ∘ preserves-meets-sups-hom-Frame

  preserves-sups-hom-Frame : (H : hom-Frame) → preserves-sups (sup-lattice-Frame A) (sup-lattice-Frame B) (map-hom-Frame H)
  preserves-sups-hom-Frame = pr2 ∘ preserves-meets-sups-hom-Frame

```
