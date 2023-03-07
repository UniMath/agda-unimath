# Truncation images of maps

```agda
module foundation.truncation-images-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
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

{-
  extensionality-trunc-im :
    (x y : A) →
    ( unit-trunc-im (succ-𝕋 k) f x ＝ unit-trunc-im (succ-𝕋 k) f y) ≃
    ( Eq-unit-trunc-im x y)
  extensionality-trunc-im x y =
    ( equiv-tot
      ( λ q →
        {!!})) ∘e
    ( equiv-pair-eq-Σ
      ( unit-trunc-im (succ-𝕋 k) f x)
      ( unit-trunc-im (succ-𝕋 k) f y))
-}
```
