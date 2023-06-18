# Homomorphisms of frames

```agda
module order-theory.homomorphisms-frames where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import order-theory.frames
open import order-theory.homomorphisms-meet-semilattices
open import order-theory.homomorphisms-meet-sup-lattices
open import order-theory.homomorphisms-sup-lattices
open import order-theory.order-preserving-maps-posets
```

</details>

## Idea

A **frame homomorphism** is an order preserving map between posets that
additionally preserves binary meets and arbitrary joins.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Frame l1 l2) (B : Frame l3 l4)
  where

  hom-Frame : UU (l1 ⊔ lsuc l2 ⊔ l3)
  hom-Frame = Σ (type-Frame A → type-Frame B)
    (λ f → preserves-order-Poset (poset-Frame A) (poset-Frame B) f ×
      preserves-meets-sups
        ( meet-suplattice-Frame A)
        ( meet-suplattice-Frame B)
        ( f))

  map-hom-Frame : hom-Frame → type-Frame A → type-Frame B
  map-hom-Frame = pr1

  preserves-order-hom-Frame :
    (H : hom-Frame) →
    preserves-order-Poset (poset-Frame A) (poset-Frame B) (map-hom-Frame H)
  preserves-order-hom-Frame = pr1 ∘ pr2

  preserves-meets-sups-hom-Frame :
    (H : hom-Frame) →
    preserves-meets-sups
      ( meet-suplattice-Frame A)
      ( meet-suplattice-Frame B)
      ( map-hom-Frame H)
  preserves-meets-sups-hom-Frame = pr2 ∘ pr2

  preserves-meets-hom-Frame :
    (H : hom-Frame) →
    preserves-meet
      ( meet-semilattice-Frame A)
      ( meet-semilattice-Frame B)
      ( map-hom-Frame H)
  preserves-meets-hom-Frame = pr1 ∘ preserves-meets-sups-hom-Frame

  preserves-sups-hom-Frame :
    (H : hom-Frame) →
    preserves-sups
      ( suplattice-Frame A)
      ( suplattice-Frame B)
      ( map-hom-Frame H)
  preserves-sups-hom-Frame = pr2 ∘ preserves-meets-sups-hom-Frame
```
