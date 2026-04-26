# Cartesian products of species of types

```agda
module species.cartesian-products-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import species.cartesian-exponents-species-of-types
open import species.morphisms-species-of-types
open import species.species-of-types
```

</details>

## Idea

The
{{#concept "cartesian product" Disambiguation="of species of types" Agda=product-species-types}}
of two [species of types](species.species-of-types.md) `F` and `G` is their
pointwise [cartesian product](foundation.cartesian-product-types.md).

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
  (F : species-types l1 l2)
  (G : species-types l1 l3)
  (H : species-types l1 l4) →
  hom-species-types (product-species-types F G) H ≃
  hom-species-types F (function-species-types G H)
equiv-universal-property-exponents-species-types F G H =
  equiv-Π-equiv-family (λ X → equiv-ev-pair)
```
