# Homomorphisms Meet Semilattices

```agda
module order-theory.homomorphisms-meet-semilattices where
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
open import order-theory.meet-semilattices
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea
A meet semi-lattice homomorphism is an order preserving map between the underlying posets that also preserves meets.

```agda

module _
  {l1 l2 l3 l4 : Level} (A : Meet-Semilattice l1 l2) (B : Meet-Semilattice l3 l4)
  where

  preserves-meets : (element-Meet-Semilattice A → element-Meet-Semilattice B) → UU (l1 ⊔ l3 ⊔ l4)
  preserves-meets f = (x y : element-Meet-Semilattice A) →
    is-greatest-binary-lower-bound-Poset (poset-Meet-Semilattice B) (f x) (f y) (f (meet-Meet-Semilattice A x y))

  hom-Meet-Semilattice : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Meet-Semilattice = Σ (element-Meet-Semilattice A → element-Meet-Semilattice B)
    λ f → preserves-order-Poset (poset-Meet-Semilattice A) (poset-Meet-Semilattice B) f × preserves-meets f

  map-hom-Meet-Semilattice : hom-Meet-Semilattice → element-Meet-Semilattice A → element-Meet-Semilattice B
  map-hom-Meet-Semilattice = pr1

  preserves-order-hom-Meet-Semilattice : (H : hom-Meet-Semilattice) →
    preserves-order-Poset (poset-Meet-Semilattice A) (poset-Meet-Semilattice B) (map-hom-Meet-Semilattice H)
  preserves-order-hom-Meet-Semilattice = pr1 ∘ pr2

  preserves-meet-hom-Meet-Semilattice : (H : hom-Meet-Semilattice) → preserves-meets (map-hom-Meet-Semilattice H)
  preserves-meet-hom-Meet-Semilattice = pr2 ∘ pr2

```
