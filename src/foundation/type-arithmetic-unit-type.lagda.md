# Type arithmetic with the unit type

```agda
module foundation.type-arithmetic-unit-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
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
  map-left-unit-law-Σ (_ , a) = a

  map-inv-left-unit-law-Σ : A star → Σ unit A
  pr1 (map-inv-left-unit-law-Σ a) = star
  pr2 (map-inv-left-unit-law-Σ a) = a

  is-section-map-inv-left-unit-law-Σ :
    ( map-left-unit-law-Σ ∘ map-inv-left-unit-law-Σ) ~ id
  is-section-map-inv-left-unit-law-Σ = refl-htpy

  is-retraction-map-inv-left-unit-law-Σ :
    ( map-inv-left-unit-law-Σ ∘ map-left-unit-law-Σ) ~ id
  is-retraction-map-inv-left-unit-law-Σ = refl-htpy

  is-equiv-map-left-unit-law-Σ : is-equiv map-left-unit-law-Σ
  is-equiv-map-left-unit-law-Σ =
    is-equiv-is-invertible
      map-inv-left-unit-law-Σ
      is-section-map-inv-left-unit-law-Σ
      is-retraction-map-inv-left-unit-law-Σ

  left-unit-law-Σ : Σ unit A ≃ A star
  pr1 left-unit-law-Σ = map-left-unit-law-Σ
  pr2 left-unit-law-Σ = is-equiv-map-left-unit-law-Σ

  is-equiv-map-inv-left-unit-law-Σ : is-equiv map-inv-left-unit-law-Σ
  is-equiv-map-inv-left-unit-law-Σ =
    is-equiv-is-invertible
      map-left-unit-law-Σ
      is-retraction-map-inv-left-unit-law-Σ
      is-section-map-inv-left-unit-law-Σ

  inv-left-unit-law-Σ : A star ≃ Σ unit A
  pr1 inv-left-unit-law-Σ = map-inv-left-unit-law-Σ
  pr2 inv-left-unit-law-Σ = is-equiv-map-inv-left-unit-law-Σ
```

### Left unit law for cartesian products

```agda
module _
  {l : Level} {A : UU l}
  where

  map-left-unit-law-product : unit × A → A
  map-left-unit-law-product = pr2

  map-inv-left-unit-law-product : A → unit × A
  map-inv-left-unit-law-product = map-inv-left-unit-law-Σ (λ _ → A)

  is-section-map-inv-left-unit-law-product :
    is-section map-left-unit-law-product map-inv-left-unit-law-product
  is-section-map-inv-left-unit-law-product =
    is-section-map-inv-left-unit-law-Σ (λ _ → A)

  is-retraction-map-inv-left-unit-law-product :
    is-retraction map-left-unit-law-product map-inv-left-unit-law-product
  is-retraction-map-inv-left-unit-law-product = refl-htpy

  is-equiv-map-left-unit-law-product : is-equiv map-left-unit-law-product
  is-equiv-map-left-unit-law-product =
    is-equiv-is-invertible
      map-inv-left-unit-law-product
      is-section-map-inv-left-unit-law-product
      is-retraction-map-inv-left-unit-law-product

  left-unit-law-product : (unit × A) ≃ A
  pr1 left-unit-law-product = map-left-unit-law-product
  pr2 left-unit-law-product = is-equiv-map-left-unit-law-product

  is-equiv-map-inv-left-unit-law-product :
    is-equiv map-inv-left-unit-law-product
  is-equiv-map-inv-left-unit-law-product =
    is-equiv-is-invertible
      map-left-unit-law-product
      is-retraction-map-inv-left-unit-law-product
      is-section-map-inv-left-unit-law-product

  inv-left-unit-law-product : A ≃ (unit × A)
  pr1 inv-left-unit-law-product = map-inv-left-unit-law-product
  pr2 inv-left-unit-law-product = is-equiv-map-inv-left-unit-law-product
```

### Right unit law for cartesian products

```agda
  map-right-unit-law-product : A × unit → A
  map-right-unit-law-product = pr1

  map-inv-right-unit-law-product : A → A × unit
  pr1 (map-inv-right-unit-law-product a) = a
  pr2 (map-inv-right-unit-law-product a) = star

  is-section-map-inv-right-unit-law-product :
    is-section map-right-unit-law-product map-inv-right-unit-law-product
  is-section-map-inv-right-unit-law-product = refl-htpy

  is-retraction-map-inv-right-unit-law-product :
    is-retraction map-right-unit-law-product map-inv-right-unit-law-product
  is-retraction-map-inv-right-unit-law-product = refl-htpy

  is-equiv-map-right-unit-law-product : is-equiv map-right-unit-law-product
  is-equiv-map-right-unit-law-product =
    is-equiv-is-invertible
      map-inv-right-unit-law-product
      is-section-map-inv-right-unit-law-product
      is-retraction-map-inv-right-unit-law-product

  right-unit-law-product : (A × unit) ≃ A
  pr1 right-unit-law-product = map-right-unit-law-product
  pr2 right-unit-law-product = is-equiv-map-right-unit-law-product
```

### Left unit law for dependent function types

```agda
module _
  {l : Level} (A : unit → UU l)
  where

  map-left-unit-law-Π : ((t : unit) → A t) → A star
  map-left-unit-law-Π f = f star

  map-inv-left-unit-law-Π : A star → ((t : unit) → A t)
  map-inv-left-unit-law-Π a _ = a

  is-section-map-inv-left-unit-law-Π :
    is-section map-left-unit-law-Π map-inv-left-unit-law-Π
  is-section-map-inv-left-unit-law-Π = refl-htpy

  is-retraction-map-inv-left-unit-law-Π :
    is-retraction map-left-unit-law-Π map-inv-left-unit-law-Π
  is-retraction-map-inv-left-unit-law-Π = refl-htpy

  is-equiv-map-left-unit-law-Π : is-equiv map-left-unit-law-Π
  is-equiv-map-left-unit-law-Π =
    is-equiv-is-invertible
      map-inv-left-unit-law-Π
      is-section-map-inv-left-unit-law-Π
      is-retraction-map-inv-left-unit-law-Π

  left-unit-law-Π : ((t : unit) → A t) ≃ A star
  pr1 left-unit-law-Π = map-left-unit-law-Π
  pr2 left-unit-law-Π = is-equiv-map-left-unit-law-Π

  is-equiv-map-inv-left-unit-law-Π : is-equiv map-inv-left-unit-law-Π
  is-equiv-map-inv-left-unit-law-Π =
    is-equiv-is-invertible
      map-left-unit-law-Π
      is-retraction-map-inv-left-unit-law-Π
      is-section-map-inv-left-unit-law-Π

  inv-left-unit-law-Π : A star ≃ ((t : unit) → A t)
  pr1 inv-left-unit-law-Π = map-inv-left-unit-law-Π
  pr2 inv-left-unit-law-Π = is-equiv-map-inv-left-unit-law-Π
```

### Left unit law for nondependent function types

```agda
module _
  {l : Level} (A : UU l)
  where

  map-left-unit-law-function-type : (unit → A) → A
  map-left-unit-law-function-type = map-left-unit-law-Π (λ _ → A)

  map-inv-left-unit-law-function-type : A → (unit → A)
  map-inv-left-unit-law-function-type = map-inv-left-unit-law-Π (λ _ → A)

  is-equiv-map-left-unit-law-function-type :
    is-equiv map-left-unit-law-function-type
  is-equiv-map-left-unit-law-function-type =
    is-equiv-map-left-unit-law-Π (λ _ → A)

  is-equiv-map-inv-left-unit-law-function-type :
    is-equiv map-inv-left-unit-law-function-type
  is-equiv-map-inv-left-unit-law-function-type =
    is-equiv-map-inv-left-unit-law-Π (λ _ → A)

  left-unit-law-function-type : (unit → A) ≃ A
  left-unit-law-function-type = left-unit-law-Π (λ _ → A)

  inv-left-unit-law-function-type : A ≃ (unit → A)
  inv-left-unit-law-function-type = inv-left-unit-law-Π (λ _ → A)
```

## See also

- That `unit` is the terminal type is a corollary of `is-contr-Π`, which may be
  found in
  [`foundation-core.contractible-types`](foundation-core.contractible-types.md).
  This can be considered a _right zero law for function types_
  (`(A → unit) ≃ unit`).
