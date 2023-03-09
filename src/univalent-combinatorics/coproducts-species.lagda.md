# Coproducts of species

```agda
module univalent-combinatorics.coproducts-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.morphisms-species
open import univalent-combinatorics.species
```

</details>

## Idea

The coproduct of two species `F` and `G` is the pointwise coproduct.

## Definition

### coproduct on objects

```agda
coprod-species :
  {l1 l2 l3 : Level} (F : species l1 l2) (G : species l1 l3) →
  species l1 (l2 ⊔ l3)
coprod-species F G X = F X + G X
```

## Universal properties

Proof of (hom-species (species-coprod F G) H) ≃ ((hom-species F H) × (hom-species G H)).

```agda
equiv-universal-property-coproduct-species :
 {l1 l2 l3 l4 : Level}
 (F : species l1 l2) (G : species l1 l3) (H : species l1 l4) →
 hom-species (coprod-species F G) H ≃ ((hom-species F H) × (hom-species G H))
equiv-universal-property-coproduct-species F G H =
  ( distributive-Π-Σ) ∘e
  ( equiv-map-Π (λ X → equiv-universal-property-coprod (H X)))
