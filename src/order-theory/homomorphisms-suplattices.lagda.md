# Homomorphisms of suplattices

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory.homomorphisms-suplattices
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets funext univalence truncations
open import order-theory.order-preserving-maps-posets funext univalence truncations
open import order-theory.suplattices funext univalence truncations
```

</details>

## Idea

A **homomorphism of suplattices** is a order preserving map between the
underlying posets that preserves least upper bounds.

## Definitions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Suplattice l1 l2 l3) (B : Suplattice l4 l5 l6)
  where

  preserves-sups :
    (type-Suplattice A → type-Suplattice B) →
    UU (l1 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  preserves-sups f =
    {I : UU l3} → (b : I → type-Suplattice A) →
    is-least-upper-bound-family-of-elements-Poset
      ( poset-Suplattice B)
      ( f ∘ b)
      ( f (sup-Suplattice A b))

  hom-Suplattice : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
  hom-Suplattice =
    Σ ( type-Suplattice A → type-Suplattice B)
      ( λ f →
        preserves-order-Poset (poset-Suplattice A) (poset-Suplattice B) f ×
        preserves-sups f)

  map-hom-Suplattice :
    hom-Suplattice → type-Suplattice A → type-Suplattice B
  map-hom-Suplattice = pr1

  preserves-order-hom-Suplattice :
    (H : hom-Suplattice) →
    preserves-order-Poset
      ( poset-Suplattice A)
      ( poset-Suplattice B)
      ( map-hom-Suplattice H)
  preserves-order-hom-Suplattice = pr1 ∘ pr2

  preserves-sup-hom-Suplattice :
    (H : hom-Suplattice) → preserves-sups (map-hom-Suplattice H)
  preserves-sup-hom-Suplattice = pr2 ∘ pr2
```
