# Diagonal maps into cartesian products of types

```agda
module foundation-core.diagonal-maps-cartesian-products-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

The diagonal map `δ : A → A × A` of `A` is the map that includes `A` as the
diagonal into `A × A`.

## Definition

```agda
module _
  {l : Level} (A : UU l)
  where

  diagonal-product : A → A × A
  diagonal-product x = (x , x)
```

## Properties

### The action on paths of a diagonal

```agda
compute-ap-diagonal-product :
  {l : Level} {A : UU l} {x y : A} (p : x ＝ y) →
  ap (diagonal-product A) p ＝ eq-pair p p
compute-ap-diagonal-product refl = refl
```

### If the diagonal of `A` is an equivalence, then `A` is a proposition

```agda
module _
  {l : Level} (A : UU l)
  where

  abstract
    is-prop-is-equiv-diagonal-product :
      is-equiv (diagonal-product A) → is-prop A
    is-prop-is-equiv-diagonal-product is-equiv-d =
      is-prop-all-elements-equal
        ( λ x y →
          ( inv (ap pr1 (is-section-map-inv-is-equiv is-equiv-d (x , y)))) ∙
          ( ap pr2 (is-section-map-inv-is-equiv is-equiv-d (x , y))))

  equiv-diagonal-product-is-prop :
    is-prop A → A ≃ A × A
  pr1 (equiv-diagonal-product-is-prop is-prop-A) =
    diagonal-product A
  pr2 (equiv-diagonal-product-is-prop is-prop-A) =
    is-equiv-is-invertible
      ( pr1)
      ( λ pair-a → eq-pair (eq-is-prop is-prop-A) (eq-is-prop is-prop-A))
      ( λ a → eq-is-prop is-prop-A)
```

### The fibers of the diagonal map

```agda
module _
  {l : Level} (A : UU l)
  where

  eq-fiber-diagonal-product :
    (t : A × A) → fiber (diagonal-product A) t → pr1 t ＝ pr2 t
  eq-fiber-diagonal-product (x , y) (z , α) = inv (ap pr1 α) ∙ ap pr2 α

  fiber-diagonal-product-eq :
    (t : A × A) → pr1 t ＝ pr2 t → fiber (diagonal-product A) t
  fiber-diagonal-product-eq (x , y) β = (x , eq-pair refl β)

  is-section-fiber-diagonal-product-eq :
    (t : A × A) →
    is-section (eq-fiber-diagonal-product t) (fiber-diagonal-product-eq t)
  is-section-fiber-diagonal-product-eq (x , .x) refl = refl

  is-retraction-fiber-diagonal-product-eq :
    (t : A × A) →
    is-retraction (eq-fiber-diagonal-product t) (fiber-diagonal-product-eq t)
  is-retraction-fiber-diagonal-product-eq .(z , z) (z , refl) = refl

  abstract
    is-equiv-eq-fiber-diagonal-product :
      (t : A × A) → is-equiv (eq-fiber-diagonal-product t)
    is-equiv-eq-fiber-diagonal-product t =
      is-equiv-is-invertible
        ( fiber-diagonal-product-eq t)
        ( is-section-fiber-diagonal-product-eq t)
        ( is-retraction-fiber-diagonal-product-eq t)
```
