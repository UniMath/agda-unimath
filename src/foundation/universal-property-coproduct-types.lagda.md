# The universal property of coproduct types

```agda
module foundation.universal-property-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

The universal property and dependent universal property of coproduct types characterize maps and dependent functions out of coproduct types.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  ev-inl-inr :
    {l3 : Level} (P : A + B → UU l3) →
    ((t : A + B) → P t) → ((x : A) → P (inl x)) × ((y : B) → P (inr y))
  ev-inl-inr P s = pair (λ x → s (inl x)) (λ y → s (inr y))

  abstract
    dependent-universal-property-coprod :
      {l3 : Level} (P : A + B → UU l3) → is-equiv (ev-inl-inr P)
    dependent-universal-property-coprod P =
      is-equiv-has-inverse
        ( λ p → ind-coprod P (pr1 p) (pr2 p))
        ( ind-Σ (λ f g → eq-pair refl refl))
        ( λ s → eq-htpy (ind-coprod _ (λ x → refl) λ y → refl))

  equiv-dependent-universal-property-coprod :
    {l3 : Level} (P : A + B → UU l3) →
    ((x : A + B) → P x) ≃ (((a : A) → P (inl a)) × ((b : B) → P (inr b)))
  pr1 (equiv-dependent-universal-property-coprod P) = ev-inl-inr P
  pr2 (equiv-dependent-universal-property-coprod P) =
    dependent-universal-property-coprod P

  abstract
    universal-property-coprod :
      {l3 : Level} (X : UU l3) →
      is-equiv (ev-inl-inr (λ (t : A + B) → X))
    universal-property-coprod X = dependent-universal-property-coprod (λ t → X)

  equiv-universal-property-coprod :
    {l3 : Level} (X : UU l3) →
    (A + B → X) ≃ ((A → X) × (B → X))
  equiv-universal-property-coprod X =
    equiv-dependent-universal-property-coprod (λ t → X)

  abstract
    uniqueness-coprod :
      {l3 : Level} {Y : UU l3} (i : A → Y) (j : B → Y) →
      ((l : Level) (X : UU l) →
        is-equiv (λ (s : Y → X) → pair' (s ∘ i) (s ∘ j))) →
      is-equiv (ind-coprod (λ t → Y) i j)
    uniqueness-coprod {Y = Y} i j H =
      is-equiv-is-equiv-precomp
        ( ind-coprod _ i j)
        ( λ l X → is-equiv-right-factor
          ( ev-inl-inr (λ t → X))
          ( precomp (ind-coprod (λ t → Y) i j) X)
          ( universal-property-coprod X)
          ( H _ X))

  abstract
    universal-property-coprod-is-equiv-ind-coprod :
      {l3 : Level} (X : UU l3) (i : A → X) (j : B → X) →
      is-equiv (ind-coprod (λ t → X) i j) →
      (l4 : Level) (Y : UU l4) →
        is-equiv (λ (s : X → Y) → pair' (s ∘ i) (s ∘ j))
    universal-property-coprod-is-equiv-ind-coprod X i j H l Y =
      is-equiv-comp
        ( ev-inl-inr (λ t → Y))
        ( precomp (ind-coprod (λ t → X) i j) Y)
        ( is-equiv-precomp-is-equiv
          ( ind-coprod (λ t → X) i j)
          ( H)
          ( Y))
        ( universal-property-coprod Y)
```
