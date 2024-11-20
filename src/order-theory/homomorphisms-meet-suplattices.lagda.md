# Homomorphisms of meet sup lattices

```agda
module order-theory.homomorphisms-meet-suplattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import order-theory.homomorphisms-meet-semilattices
open import order-theory.homomorphisms-suplattices
open import order-theory.meet-suplattices
open import order-theory.order-preserving-maps-posets
```

</details>

## Idea

A **homomorphism of meet-suplattices** is a homomorphism of meet-semilattices
that in addition preserves least upper bounds.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Meet-Suplattice l1 l2)
  (B : Meet-Suplattice l3 l4)
  where

  preserves-meets-sups :
    (type-Meet-Suplattice A → type-Meet-Suplattice B) →
    UU (l1 ⊔ lsuc l2 ⊔ l3)
  preserves-meets-sups f =
    preserves-meet
      ( meet-semilattice-Meet-Suplattice A)
      ( meet-semilattice-Meet-Suplattice B)
      ( f) ×
    preserves-sups
      ( suplattice-Meet-Suplattice A)
      ( suplattice-Meet-Suplattice B)
      ( f)

  hom-Meet-Suplattice : UU (l1 ⊔ lsuc l2 ⊔ l3)
  hom-Meet-Suplattice =
    Σ ( type-Meet-Suplattice A → type-Meet-Suplattice B)
      ( λ f →
        preserves-order-Poset
          ( poset-Meet-Suplattice A)
          ( poset-Meet-Suplattice B)
          ( f) ×
        ( preserves-meets-sups f))

  map-hom-Meet-Suplattice :
    hom-Meet-Suplattice →
    type-Meet-Suplattice A → type-Meet-Suplattice B
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
    preserves-meet
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
