# Cartesian products of species

```agda
module univalent-combinatorics.cartesian-products-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.equivalences-species
open import univalent-combinatorics.exponents-species
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.morphisms-species
open import univalent-combinatorics.species
```

</details>

## Idea

The cartesian product of two species `F` and `G` is their pointwise cartesian product.

## Definition

```agda
prod-species :
  {l1 l2 l3 : Level} (F : species l1 l2) (G : species l1 l3) →
  species l1 (l2 ⊔ l3)
prod-species F G X = (F X) × (G X)
```

## Properties

### The adjunction between cartesian products and exponents of species

```agda
equiv-universal-property-exponents-species :
  {l1 l2 l3 l4 : Level}
  (F : species l1 l2) (G : species l1 l3) (H : species l1 l4) →
  hom-species (prod-species F G) H ≃ hom-species F (function-species G H)
equiv-universal-property-exponents-species F G H =
  equiv-map-Π (λ X → equiv-ev-pair)
```
