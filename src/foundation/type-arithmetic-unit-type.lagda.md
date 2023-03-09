# Type arithmetic with the unit type

```agda
module foundation.type-arithmetic-unit-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.unit-type

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universe-levels
```

</details>

## Idea

We prove arithmetical laws involving the unit type

## Laws

### Left unit law for dependent pair types

```agda
module _
  {l : Level} (A : unit → UU l)
  where

  map-left-unit-law-Σ : Σ unit A → A star
  map-left-unit-law-Σ (pair star a) = a

  map-inv-left-unit-law-Σ : A star → Σ unit A
  pr1 (map-inv-left-unit-law-Σ a) = star
  pr2 (map-inv-left-unit-law-Σ a) = a

  issec-map-inv-left-unit-law-Σ :
    ( map-left-unit-law-Σ ∘ map-inv-left-unit-law-Σ) ~ id
  issec-map-inv-left-unit-law-Σ a = refl

  isretr-map-inv-left-unit-law-Σ :
    ( map-inv-left-unit-law-Σ ∘ map-left-unit-law-Σ) ~ id
  isretr-map-inv-left-unit-law-Σ (pair star a) = refl

  is-equiv-map-left-unit-law-Σ : is-equiv map-left-unit-law-Σ
  is-equiv-map-left-unit-law-Σ =
    is-equiv-has-inverse
      map-inv-left-unit-law-Σ
      issec-map-inv-left-unit-law-Σ
      isretr-map-inv-left-unit-law-Σ

  left-unit-law-Σ : Σ unit A ≃ A star
  pr1 left-unit-law-Σ = map-left-unit-law-Σ
  pr2 left-unit-law-Σ = is-equiv-map-left-unit-law-Σ

  is-equiv-map-inv-left-unit-law-Σ : is-equiv map-inv-left-unit-law-Σ
  is-equiv-map-inv-left-unit-law-Σ =
    is-equiv-has-inverse
      map-left-unit-law-Σ
      isretr-map-inv-left-unit-law-Σ
      issec-map-inv-left-unit-law-Σ

  inv-left-unit-law-Σ : A star ≃ Σ unit A
  pr1 inv-left-unit-law-Σ = map-inv-left-unit-law-Σ
  pr2 inv-left-unit-law-Σ = is-equiv-map-inv-left-unit-law-Σ
```

### Left unit law for cartesian products

```agda
module _
  {l : Level} {A : UU l}
  where

  map-left-unit-law-prod : unit × A → A
  map-left-unit-law-prod = pr2

  map-inv-left-unit-law-prod : A → unit × A
  map-inv-left-unit-law-prod = map-inv-left-unit-law-Σ (λ x → A)

  issec-map-inv-left-unit-law-prod :
    ( map-left-unit-law-prod ∘ map-inv-left-unit-law-prod) ~ id
  issec-map-inv-left-unit-law-prod =
    issec-map-inv-left-unit-law-Σ (λ x → A)

  isretr-map-inv-left-unit-law-prod :
    ( map-inv-left-unit-law-prod ∘ map-left-unit-law-prod) ~ id
  isretr-map-inv-left-unit-law-prod (pair star a) = refl

  is-equiv-map-left-unit-law-prod : is-equiv map-left-unit-law-prod
  is-equiv-map-left-unit-law-prod =
    is-equiv-has-inverse
      map-inv-left-unit-law-prod
      issec-map-inv-left-unit-law-prod
      isretr-map-inv-left-unit-law-prod

  left-unit-law-prod : (unit × A) ≃ A
  pr1 left-unit-law-prod = map-left-unit-law-prod
  pr2 left-unit-law-prod = is-equiv-map-left-unit-law-prod

  is-equiv-map-inv-left-unit-law-prod : is-equiv map-inv-left-unit-law-prod
  is-equiv-map-inv-left-unit-law-prod =
    is-equiv-has-inverse
      map-left-unit-law-prod
      isretr-map-inv-left-unit-law-prod
      issec-map-inv-left-unit-law-prod

  inv-left-unit-law-prod : A ≃ (unit × A)
  pr1 inv-left-unit-law-prod = map-inv-left-unit-law-prod
  pr2 inv-left-unit-law-prod = is-equiv-map-inv-left-unit-law-prod
```

### Right unit law for cartesian products

```agda
  map-right-unit-law-prod : A × unit → A
  map-right-unit-law-prod = pr1

  map-inv-right-unit-law-prod : A → A × unit
  pr1 (map-inv-right-unit-law-prod a) = a
  pr2 (map-inv-right-unit-law-prod a) = star

  issec-map-inv-right-unit-law-prod :
    (map-right-unit-law-prod ∘ map-inv-right-unit-law-prod) ~ id
  issec-map-inv-right-unit-law-prod a = refl

  isretr-map-inv-right-unit-law-prod :
    (map-inv-right-unit-law-prod ∘ map-right-unit-law-prod) ~ id
  isretr-map-inv-right-unit-law-prod (pair a star) = refl

  is-equiv-map-right-unit-law-prod : is-equiv map-right-unit-law-prod
  is-equiv-map-right-unit-law-prod =
    is-equiv-has-inverse
      map-inv-right-unit-law-prod
      issec-map-inv-right-unit-law-prod
      isretr-map-inv-right-unit-law-prod

  right-unit-law-prod : (A × unit) ≃ A
  pr1 right-unit-law-prod = map-right-unit-law-prod
  pr2 right-unit-law-prod = is-equiv-map-right-unit-law-prod
```

### Left unit law for dependent function types

```agda
module _
  {l : Level} (A : unit → UU l)
  where

  map-left-unit-law-Π : ((t : unit) → A t) → A star
  map-left-unit-law-Π f = f star

  map-inv-left-unit-law-Π : A star → ((t : unit) → A t)
  map-inv-left-unit-law-Π a star = a

  issec-map-inv-left-unit-law-Π :
    ( map-left-unit-law-Π ∘ map-inv-left-unit-law-Π) ~ id
  issec-map-inv-left-unit-law-Π a = refl

  isretr-map-inv-left-unit-law-Π :
    ( map-inv-left-unit-law-Π ∘ map-left-unit-law-Π) ~ id
  isretr-map-inv-left-unit-law-Π f = eq-htpy (λ { star → refl })

  is-equiv-map-left-unit-law-Π : is-equiv map-left-unit-law-Π
  is-equiv-map-left-unit-law-Π =
    is-equiv-has-inverse
      map-inv-left-unit-law-Π
      issec-map-inv-left-unit-law-Π
      isretr-map-inv-left-unit-law-Π

  left-unit-law-Π : ((t : unit) → A t) ≃ A star
  pr1 left-unit-law-Π = map-left-unit-law-Π
  pr2 left-unit-law-Π = is-equiv-map-left-unit-law-Π

  is-equiv-map-inv-left-unit-law-Π : is-equiv map-inv-left-unit-law-Π
  is-equiv-map-inv-left-unit-law-Π =
    is-equiv-has-inverse
      map-left-unit-law-Π
      isretr-map-inv-left-unit-law-Π
      issec-map-inv-left-unit-law-Π

  inv-left-unit-law-Π : A star ≃ ((t : unit) → A t)
  pr1 inv-left-unit-law-Π = map-inv-left-unit-law-Π
  pr2 inv-left-unit-law-Π = is-equiv-map-inv-left-unit-law-Π
```

### Left unit law for non-dependent function types

```agda
module _
  {l : Level} (A : UU l)
  where

  left-unit-law-function-types : (unit → A) ≃ A
  left-unit-law-function-types = left-unit-law-Π (λ _ → A)

  inv-left-unit-law-function-types : A ≃ (unit → A)
  inv-left-unit-law-function-types = inv-left-unit-law-Π (λ _ → A)
```

## See also

- That `unit` is the terminal type is a corollary of `is-contr-Π`, which may be found in
  [`foundation-core.contractible-types`](foundation-core.contractible-types.md).
  This can be considered a *right zero law for function types* (`(A → unit) ≃ unit`).
