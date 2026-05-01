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

The
{{#concept "coproduct" Disambiguation="of species of types" Agda=coproduct-species-types}}
of two [species of types](species.species-of-types.md) `F` and `G` is the
pointwise [coproduct](foundation.coproduct-types.md).

## Definition

### Coproduct on objects

```agda
coproduct-species-types :
  {l1 l2 l3 : Level} (F : species-types l1 l2) (G : species-types l1 l3) →
  species-types l1 (l2 ⊔ l3)
coproduct-species-types F G X = (F X + G X)
```

## Universal properties

Proof of

```text
  (hom-species-types (species-types-coproduct F G) H) ≃
  ((hom-species-types F H) × (hom-species-types G H)).
```

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
  ( equiv-Π-equiv-family (λ X → equiv-universal-property-coproduct (H X)))
```
