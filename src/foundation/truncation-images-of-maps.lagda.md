# Truncation images of maps

<details><summary>Imports</summary>
```agda
module foundation.truncation-images-of-maps where
open import foundation.connected-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.truncated-maps
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels
```
</details>

## Idea

The **`k`-truncation image** of a map `f : A → B` is the type `trunc-im k f` that fits in the (`k`-connected,`k`-truncated) factorization of `f`. It is defined as the type

```md
  trunc-im k f := Σ (y : B), type-trunc k (fib f y)
```

## Definition

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  trunc-im : UU (l1 ⊔ l2)
  trunc-im = Σ B (λ y → type-trunc k (fib f y))

  unit-trunc-im : A → trunc-im
  pr1 (unit-trunc-im x) = f x
  pr2 (unit-trunc-im x) = unit-trunc (pair x refl)

  projection-trunc-im : trunc-im → B
  projection-trunc-im = pr1
```

## Properties

### Characterization of the identity types of `k+1`-truncation images

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  Eq-unit-trunc-im : A → A → UU (l1 ⊔ l2)
  Eq-unit-trunc-im x y = trunc-im k (ap f {x} {y})

  extensionality-trunc-im :
    (x y : A) →
    ( unit-trunc-im (succ-𝕋 k) f x ＝ unit-trunc-im (succ-𝕋 k) f y) ≃
    ( Eq-unit-trunc-im x y)
  extensionality-trunc-im x y =
    ( equiv-tot
      ( λ q →
        equiv-trunc k (equiv-tot (λ p → equiv-concat (inv right-unit) q) ∘e equiv-Eq-eq-fib f (f y)) ∘e
        ( inv-equiv (effectiveness-trunc k (x , q) (y , refl)) ∘e
          ( equiv-concat (ap unit-trunc (inv (tr-fib f q refl))) (unit-trunc (y , refl)) ∘e
            equiv-concat (preserves-tr (λ _ → unit-trunc) q (x , refl)) (unit-trunc (y , refl)))))) ∘e
    ( equiv-pair-eq-Σ
      ( unit-trunc-im (succ-𝕋 k) f x)
      ( unit-trunc-im (succ-𝕋 k) f y))
```

### The map projection-trunc-im k is k-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-trunc-map-projection-trunc-im : is-trunc-map k (projection-trunc-im k f)
  is-trunc-map-projection-trunc-im = is-trunc-map-pr1 k (λ _ → is-trunc-type-trunc)
```

### The map unit-trunc-im k is k-connected

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-unit-trunc-im : is-connected-map k (unit-trunc-im k f)
  is-connected-map-unit-trunc-im =
    is-connected-map-comp k _ _
      ( is-connected-map-tot-is-fiberwise-connected-map k
        ( λ b → unit-trunc)
        ( λ b → is-connected-map-unit-trunc k))
      ( is-connected-map-is-equiv k (is-equiv-map-inv-equiv-total-fib f))
```
