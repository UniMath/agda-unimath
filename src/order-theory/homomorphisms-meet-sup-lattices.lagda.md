# Homomorphisms of meet sup lattices

```agda
module order-theory.homomorphisms-meet-sup-lattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.universe-levels

open import order-theory.homomorphisms-meet-semilattices
open import order-theory.homomorphisms-sup-lattices
open import order-theory.infinite-distributive-law
open import order-theory.order-preserving-maps-posets
```

</details>

## Idea

A meet sup lattice homomorphism is an order preserving map between the
underlying posets that preserves meets and sup. In fact any sup lattice
neccesarily has binary meets but we have yet to give a proof of this fact in the
library. Thus, we opt (for now) to treat the two structures as existing
independently.

## Definitions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Meet-Suplattice l1 l2 l3)
  (B : Meet-Suplattice l4 l5 l6)
  where

  preserves-meets-sups :
    (element-Meet-Suplattice A → element-Meet-Suplattice B) →
    UU (l1 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  preserves-meets-sups f =
    preserves-meets
      ( meet-semilattice-Meet-Suplattice A)
      ( meet-semilattice-Meet-Suplattice B)
      ( f) ×
    preserves-sups
      ( suplattice-Meet-Suplattice A)
      ( suplattice-Meet-Suplattice B)
      ( f)

  hom-Meet-Suplattice : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  hom-Meet-Suplattice =
    Σ ( element-Meet-Suplattice A → element-Meet-Suplattice B)
      ( λ f →
        preserves-order-Poset
          ( poset-Meet-Suplattice A)
          ( poset-Meet-Suplattice B)
          ( f) ×
        ( preserves-meets-sups f))

  map-hom-Meet-Suplattice :
    hom-Meet-Suplattice →
    element-Meet-Suplattice A → element-Meet-Suplattice B
  map-hom-Meet-Suplattice = pr1

  preserves-order-Meet-Suplattice :
    (H : hom-Meet-Suplattice) →
    preserves-order-Poset
      ( poset-Meet-Suplattice A)
      ( poset-Meet-Suplattice B)
      ( map-hom-Meet-Suplattice H)
  preserves-order-Meet-Suplattice = pr1 ∘ pr2

  preserves-meets-sups-Meet-Suplattice :
    (H : hom-Meet-Suplattice) →
    preserves-meets-sups (map-hom-Meet-Suplattice H)
  preserves-meets-sups-Meet-Suplattice = pr2 ∘ pr2

  preserves-meets-Meet-Suplattice :
    (H : hom-Meet-Suplattice) →
    preserves-meets
      ( meet-semilattice-Meet-Suplattice A)
      ( meet-semilattice-Meet-Suplattice B)
      ( map-hom-Meet-Suplattice H)
  preserves-meets-Meet-Suplattice = pr1 ∘ preserves-meets-sups-Meet-Suplattice

  preserves-sups-Meet-Suplattice :
    (H : hom-Meet-Suplattice) →
    preserves-sups
      ( suplattice-Meet-Suplattice A)
      ( suplattice-Meet-Suplattice B)
      ( map-hom-Meet-Suplattice H)
  preserves-sups-Meet-Suplattice = pr2 ∘ preserves-meets-sups-Meet-Suplattice
```
