# The universal property of the maybe monad

```agda
module foundation.universal-property-maybe where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.maybe
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

We combine the
[universal property of coproducts](foundation.universal-property-coproduct-types.md)
and the [unit type](foundation.universal-property-unit-type.md) to obtain the
{{#concept "universal property of the maybe monad" Agda=dependent-universal-property-Maybe}}.

## Definitions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2}
  where

  ev-Maybe :
    ((x : Maybe A) → B x) → ((x : A) → B (unit-Maybe x)) × B exception-Maybe
  pr1 (ev-Maybe h) x = h (unit-Maybe x)
  pr2 (ev-Maybe h) = h exception-Maybe

  ind-Maybe :
    ((x : A) → B (unit-Maybe x)) × (B exception-Maybe) → (x : Maybe A) → B x
  ind-Maybe (pair h b) (inl x) = h x
  ind-Maybe (pair h b) (inr _) = b

  abstract
    is-section-ind-Maybe : (ev-Maybe ∘ ind-Maybe) ~ id
    is-section-ind-Maybe (pair h b) = refl

    is-retraction-ind-Maybe' :
      (h : (x : Maybe A) → B x) → (ind-Maybe (ev-Maybe h)) ~ h
    is-retraction-ind-Maybe' h (inl x) = refl
    is-retraction-ind-Maybe' h (inr _) = refl

    is-retraction-ind-Maybe : (ind-Maybe ∘ ev-Maybe) ~ id
    is-retraction-ind-Maybe h = eq-htpy (is-retraction-ind-Maybe' h)

    dependent-universal-property-Maybe :
      is-equiv ev-Maybe
    dependent-universal-property-Maybe =
      is-equiv-is-invertible
        ind-Maybe
        is-section-ind-Maybe
        is-retraction-ind-Maybe

equiv-dependent-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} (B : Maybe A → UU l2) →
  ((x : Maybe A) → B x) ≃ (((x : A) → B (unit-Maybe x)) × B exception-Maybe)
pr1 (equiv-dependent-universal-property-Maybe B) = ev-Maybe
pr2 (equiv-dependent-universal-property-Maybe B) =
  dependent-universal-property-Maybe

equiv-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (Maybe A → B) ≃ ((A → B) × B)
equiv-universal-property-Maybe {l1} {l2} {A} {B} =
  equiv-dependent-universal-property-Maybe (λ x → B)
```
