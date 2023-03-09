# Homomorphisms Sup Lattices

```agda
module order-theory.homomorphisms-sup-lattices where
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
open import order-theory.least-upper-bounds-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.sup-lattices
```

</details>

## Idea
A sup lattice homomorphism is a order preserving map between the underlying posets that additionally preserves sups (or arbitrary joins of subsets).

```agda

module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : Sup-Lattice l1 l2 l3) (B : Sup-Lattice l4 l5 l6)
  where

  preserves-sups : (element-Sup-Lattice A → element-Sup-Lattice B) → UU (l1 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  preserves-sups f = {I : UU l3} → (b : I → element-Sup-Lattice A) →
    is-least-upper-bound-family-Poset (poset-Sup-Lattice B) (f ∘ b) (f (sup-Sup-Lattice A I b))

  hom-Sup-Lattice : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  hom-Sup-Lattice = Σ (element-Sup-Lattice A → element-Sup-Lattice B)
    λ f → preserves-order-Poset (poset-Sup-Lattice A) (poset-Sup-Lattice B) f × preserves-sups f

  map-hom-Sup-Lattice : hom-Sup-Lattice → element-Sup-Lattice A → element-Sup-Lattice B
  map-hom-Sup-Lattice = pr1

  preserves-order-hom-Sup-Lattice : (H : hom-Sup-Lattice) → preserves-order-Poset (poset-Sup-Lattice A) (poset-Sup-Lattice B) (map-hom-Sup-Lattice H)
  preserves-order-hom-Sup-Lattice = pr1 ∘ pr2

  preserves-sup-hom-Sup-Lattice : (H : hom-Sup-Lattice) → preserves-sups (map-hom-Sup-Lattice H)
  preserves-sup-hom-Sup-Lattice = pr2 ∘ pr2

```
