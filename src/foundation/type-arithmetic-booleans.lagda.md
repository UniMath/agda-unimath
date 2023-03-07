# Type arithmetic with the booleans

```agda
module foundation.type-arithmetic-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
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

  map-Σ-bool-coprod : Σ bool A → A true + A false
  map-Σ-bool-coprod (pair true a) = inl a
  map-Σ-bool-coprod (pair false a) = inr a

  map-inv-Σ-bool-coprod : A true + A false → Σ bool A
  map-inv-Σ-bool-coprod (inl a) = pair true a
  map-inv-Σ-bool-coprod (inr a) = pair false a

  issec-map-inv-Σ-bool-coprod :
    ( map-Σ-bool-coprod ∘ map-inv-Σ-bool-coprod) ~ id
  issec-map-inv-Σ-bool-coprod (inl a) = refl
  issec-map-inv-Σ-bool-coprod (inr a) = refl

  isretr-map-inv-Σ-bool-coprod :
    ( map-inv-Σ-bool-coprod ∘ map-Σ-bool-coprod) ~ id
  isretr-map-inv-Σ-bool-coprod (pair true a) = refl
  isretr-map-inv-Σ-bool-coprod (pair false a) = refl

  is-equiv-map-Σ-bool-coprod : is-equiv map-Σ-bool-coprod
  is-equiv-map-Σ-bool-coprod =
    is-equiv-has-inverse
      map-inv-Σ-bool-coprod
      issec-map-inv-Σ-bool-coprod
      isretr-map-inv-Σ-bool-coprod

  equiv-Σ-bool-coprod : Σ bool A ≃ (A true + A false)
  pr1 equiv-Σ-bool-coprod = map-Σ-bool-coprod
  pr2 equiv-Σ-bool-coprod = is-equiv-map-Σ-bool-coprod

  is-equiv-map-inv-Σ-bool-coprod : is-equiv map-inv-Σ-bool-coprod
  is-equiv-map-inv-Σ-bool-coprod =
    is-equiv-has-inverse
      map-Σ-bool-coprod
      isretr-map-inv-Σ-bool-coprod
      issec-map-inv-Σ-bool-coprod

  inv-equiv-Σ-bool-coprod : (A true + A false) ≃ Σ bool A
  pr1 inv-equiv-Σ-bool-coprod = map-inv-Σ-bool-coprod
  pr2 inv-equiv-Σ-bool-coprod = is-equiv-map-inv-Σ-bool-coprod
```
