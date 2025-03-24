# Cartesian products of species of types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species.cartesian-products-species-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.equivalences funext
open import foundation.functoriality-dependent-function-types funext univalence
open import foundation.universal-property-dependent-pair-types funext
open import foundation.universe-levels

open import species.cartesian-exponents-species-of-types funext univalence
open import species.morphisms-species-of-types funext univalence truncations
open import species.species-of-types funext univalence
```

</details>

## Idea

The **cartesian product** of two species of types `F` and `G` is their pointwise
cartesian product.

## Definition

```agda
product-species-types :
  {l1 l2 l3 : Level} (F : species-types l1 l2) (G : species-types l1 l3) →
  species-types l1 (l2 ⊔ l3)
product-species-types F G X = (F X) × (G X)
```

## Properties

### The adjunction between cartesian products and exponents of species of types

```agda
equiv-universal-property-exponents-species-types :
  {l1 l2 l3 l4 : Level}
  (F : species-types l1 l2) (G : species-types l1 l3)
  (H : species-types l1 l4) →
  hom-species-types (product-species-types F G) H ≃
  hom-species-types F (function-species-types G H)
equiv-universal-property-exponents-species-types F G H =
  equiv-Π-equiv-family (λ X → equiv-ev-pair)
```
