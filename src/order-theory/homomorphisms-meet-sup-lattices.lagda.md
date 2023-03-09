# Homomorphisms Meet Sup Lattice

```agda
module order-theory.homomorphisms-meet-sup-lattices where
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

open import order-theory.greatest-lower-bounds-posets
open import order-theory.homomorphisms-meet-semilattices
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
A meet sup lattice homomorphism is an order preserving map between the underlying posets that preserves meets and sup.
In fact any sup lattice neccesarily has binary meets but we have yet to give a proof of this fact in the library. Thus,
we opt (for now) to treat the two structures as existing independently.

```agda

module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : Meet-Sup-Lattice l1 l2 l3) (B : Meet-Sup-Lattice l4 l5 l6)
  where

  preserves-meets-sups : (element-Meet-Sup-Lattice A → element-Meet-Sup-Lattice B) → UU (l1 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  preserves-meets-sups f =
    preserves-meets (meet-semilattice-Meet-Sup-Lattice A) (meet-semilattice-Meet-Sup-Lattice B) f ×
    preserves-sups (sup-lattice-Meet-Sup-Lattice A) (sup-lattice-Meet-Sup-Lattice B) f

  hom-Meet-Sup-Lattice : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  hom-Meet-Sup-Lattice = Σ (element-Meet-Sup-Lattice A → element-Meet-Sup-Lattice B)
    (λ f → preserves-order-Poset (poset-Meet-Sup-Lattice A) (poset-Meet-Sup-Lattice B) f × (preserves-meets-sups f))

  map-hom-Meet-Sup-Lattice : hom-Meet-Sup-Lattice → (element-Meet-Sup-Lattice A → element-Meet-Sup-Lattice B)
  map-hom-Meet-Sup-Lattice = pr1

  preserves-order-Meet-Sup-Lattice : (H : hom-Meet-Sup-Lattice) →
    preserves-order-Poset (poset-Meet-Sup-Lattice A) (poset-Meet-Sup-Lattice B) (map-hom-Meet-Sup-Lattice H)
  preserves-order-Meet-Sup-Lattice = pr1 ∘ pr2

  preserves-meets-sups-Meet-Sup-Lattice : (H : hom-Meet-Sup-Lattice) → preserves-meets-sups (map-hom-Meet-Sup-Lattice H)
  preserves-meets-sups-Meet-Sup-Lattice = pr2 ∘ pr2

  preserves-meets-Meet-Sup-Lattice : (H : hom-Meet-Sup-Lattice) →
    preserves-meets (meet-semilattice-Meet-Sup-Lattice A) (meet-semilattice-Meet-Sup-Lattice B) (map-hom-Meet-Sup-Lattice H)
  preserves-meets-Meet-Sup-Lattice = pr1 ∘ preserves-meets-sups-Meet-Sup-Lattice

  preserves-sups-Meet-Sup-Lattice : (H : hom-Meet-Sup-Lattice) →
    preserves-sups (sup-lattice-Meet-Sup-Lattice A) (sup-lattice-Meet-Sup-Lattice B) (map-hom-Meet-Sup-Lattice H)
  preserves-sups-Meet-Sup-Lattice = pr2 ∘ preserves-meets-sups-Meet-Sup-Lattice

```
