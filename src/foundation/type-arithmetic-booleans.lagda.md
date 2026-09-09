# Type arithmetic with the booleans

```agda
module foundation.type-arithmetic-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

We prove arithmetical laws involving the booleans

## Laws

### Dependent pairs over booleans are equivalent to coproducts

```agda
module _
  {l : Level} (A : bool → UU l)
  where

  map-Σ-bool-coproduct : Σ bool A → A true + A false
  map-Σ-bool-coproduct (pair true a) = inl a
  map-Σ-bool-coproduct (pair false a) = inr a

  map-inv-Σ-bool-coproduct : A true + A false → Σ bool A
  map-inv-Σ-bool-coproduct (inl a) = pair true a
  map-inv-Σ-bool-coproduct (inr a) = pair false a

  is-section-map-inv-Σ-bool-coproduct :
    ( map-Σ-bool-coproduct ∘ map-inv-Σ-bool-coproduct) ~ id
  is-section-map-inv-Σ-bool-coproduct (inl a) = refl
  is-section-map-inv-Σ-bool-coproduct (inr a) = refl

  is-retraction-map-inv-Σ-bool-coproduct :
    ( map-inv-Σ-bool-coproduct ∘ map-Σ-bool-coproduct) ~ id
  is-retraction-map-inv-Σ-bool-coproduct (pair true a) = refl
  is-retraction-map-inv-Σ-bool-coproduct (pair false a) = refl

  is-equiv-map-Σ-bool-coproduct : is-equiv map-Σ-bool-coproduct
  is-equiv-map-Σ-bool-coproduct =
    is-equiv-is-invertible
      map-inv-Σ-bool-coproduct
      is-section-map-inv-Σ-bool-coproduct
      is-retraction-map-inv-Σ-bool-coproduct

  equiv-Σ-bool-coproduct : Σ bool A ≃ (A true + A false)
  pr1 equiv-Σ-bool-coproduct = map-Σ-bool-coproduct
  pr2 equiv-Σ-bool-coproduct = is-equiv-map-Σ-bool-coproduct

  is-equiv-map-inv-Σ-bool-coproduct : is-equiv map-inv-Σ-bool-coproduct
  is-equiv-map-inv-Σ-bool-coproduct =
    is-equiv-is-invertible
      map-Σ-bool-coproduct
      is-retraction-map-inv-Σ-bool-coproduct
      is-section-map-inv-Σ-bool-coproduct

  inv-equiv-Σ-bool-coproduct : (A true + A false) ≃ Σ bool A
  pr1 inv-equiv-Σ-bool-coproduct = map-inv-Σ-bool-coproduct
  pr2 inv-equiv-Σ-bool-coproduct = is-equiv-map-inv-Σ-bool-coproduct
```

### Dependent functions over booleans are equivalent to cartesian products

```agda
module _
  {l : Level} (A : bool → UU l)
  where

  map-Π-bool-product : ((b : bool) → A b) → A true × A false
  map-Π-bool-product f = (f true , f false)

  map-inv-Π-bool-product : A true × A false → ((b : bool) → A b)
  map-inv-Π-bool-product (x , y) = ind-bool A x y

  is-section-map-inv-Π-bool-product :
    map-Π-bool-product ∘ map-inv-Π-bool-product ~ id
  is-section-map-inv-Π-bool-product = λ _ → refl

  is-retraction-map-inv-Π-bool-product :
    map-inv-Π-bool-product ∘ map-Π-bool-product ~ id
  is-retraction-map-inv-Π-bool-product = λ f → eq-htpy
    (ind-bool
    (λ b → (ind-bool A (f true) (f false)) b ＝ f b)
    refl refl)

  is-equiv-map-Π-bool-product : is-equiv map-Π-bool-product
  is-equiv-map-Π-bool-product =
    is-equiv-is-invertible
      map-inv-Π-bool-product
      is-section-map-inv-Π-bool-product
      is-retraction-map-inv-Π-bool-product

  equiv-Π-bool-product : ((b : bool) → A b) ≃ A true × A false
  pr1 equiv-Π-bool-product = map-Π-bool-product
  pr2 equiv-Π-bool-product = is-equiv-map-Π-bool-product

  is-equiv-map-inv-Π-bool-product : is-equiv map-inv-Π-bool-product
  is-equiv-map-inv-Π-bool-product =
    is-equiv-is-invertible
      map-Π-bool-product
      is-retraction-map-inv-Π-bool-product
      is-section-map-inv-Π-bool-product

  inv-equiv-Π-bool-product : (A true × A false) ≃ ((b : bool) → A b)
  pr1 inv-equiv-Π-bool-product = map-inv-Π-bool-product
  pr2 inv-equiv-Π-bool-product = is-equiv-map-inv-Π-bool-product
```
