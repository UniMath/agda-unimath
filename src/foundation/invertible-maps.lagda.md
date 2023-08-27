# Invertible maps

```agda
module foundation.invertible-maps where

open import foundation-core.invertible-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation.type-arithmetic-dependent-pair-types
open import foundation.equivalences
open import foundation.action-on-identifications-functions
open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Properties

### The type `has-inverse id` is equivalent to `id ~ id`

```agda
is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  (id {A = A} ~ id {A = A}) → has-inverse (id {A = A})
pr1 (is-invertible-id-htpy-id-id A H) = id
pr1 (pr2 (is-invertible-id-htpy-id-id A H)) = refl-htpy
pr2 (pr2 (is-invertible-id-htpy-id-id A H)) = H

triangle-is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  ( is-invertible-id-htpy-id-id A) ~
    ( ( map-associative-Σ
        ( A → A)
        ( λ g → (id ∘ g) ~ id)
        ( λ s → (pr1 s ∘ id) ~ id)) ∘
      ( map-inv-left-unit-law-Σ-is-contr
        { B = λ s → (pr1 s ∘ id) ~ id}
        ( is-contr-section-is-equiv (is-equiv-id {_} {A}))
        ( pair id refl-htpy)))
triangle-is-invertible-id-htpy-id-id A H = refl

abstract
  is-equiv-invertible-id-htpy-id-id :
    {l : Level} (A : UU l) → is-equiv (is-invertible-id-htpy-id-id A)
  is-equiv-invertible-id-htpy-id-id A =
    is-equiv-comp-htpy
      ( is-invertible-id-htpy-id-id A)
      ( map-associative-Σ
        ( A → A)
        ( λ g → (id ∘ g) ~ id)
        ( λ s → (pr1 s ∘ id) ~ id))
      ( map-inv-left-unit-law-Σ-is-contr
        ( is-contr-section-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( triangle-is-invertible-id-htpy-id-id A)
      ( is-equiv-map-inv-left-unit-law-Σ-is-contr
        ( is-contr-section-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( is-equiv-map-associative-Σ _ _ _)
```

## See also

- For the coherent notion of invertible maps see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
