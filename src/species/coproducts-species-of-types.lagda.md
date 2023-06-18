# Coproducts of species of types

```agda
module species.coproducts-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import species.morphisms-species-of-types
open import species.species-of-types
```

</details>

## Idea

The coproduct of two species of types `F` and `G` is the pointwise coproduct.

## Definition

### coproduct on objects

```agda
coproduct-species-types :
  {l1 l2 l3 : Level} (F : species-types l1 l2) (G : species-types l1 l3) →
  species-types l1 (l2 ⊔ l3)
coproduct-species-types F G X = F X + G X
```

## Universal properties

Proof of (hom-species-types (species-types-coprod F G) H) ≃ ((hom-species-types
F H) × (hom-species-types G H)).

```agda
equiv-universal-property-coproduct-species-types :
  {l1 l2 l3 l4 : Level}
  (F : species-types l1 l2)
  (G : species-types l1 l3)
  (H : species-types l1 l4) →
  hom-species-types (coproduct-species-types F G) H ≃
  ((hom-species-types F H) × (hom-species-types G H))
equiv-universal-property-coproduct-species-types F G H =
  ( distributive-Π-Σ) ∘e
  ( equiv-map-Π (λ X → equiv-universal-property-coprod (H X)))
```
