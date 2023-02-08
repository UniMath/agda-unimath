---
title: Symmetric H-spaces
---

```agda
module structured-types.symmetric-h-spaces where

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.symmetric-identity-types
open import foundation.symmetric-operations
open import foundation.universe-levels

open import structured-types.pointed-types

open import univalent-combinatorics.2-element-types
```

## Idea

We equip the type of H-space structures on a pointed type `A` with a `ℤ/2`-action. Symmetric H-spaces are defined to be the fixed points of this action.

## Definition

### The `ℤ/2`-action on `H-space (A)`

```agda
ℤ/2-action-H-Space :
  {l1 : Level} (A : Pointed-Type l1) (X : 2-Element-Type lzero) → UU l1
ℤ/2-action-H-Space A X =
  Σ ( (type-2-Element-Type X → type-Pointed-Type A) → type-Pointed-Type A)
    ( λ μ →
      Σ ( ( f : type-2-Element-Type X → type-Pointed-Type A) →
          ( x : type-2-Element-Type X) →
          ( p : f x ＝ pt-Pointed-Type A) →
          μ f ＝ f (map-swap-2-Element-Type X x))
        ( λ ν →
          symmetric-Id (X , (λ x → ν (const _ _ (pt-Pointed-Type A)) x refl))))

symmetric-H-Space :
  {l1 : Level} (A : Pointed-Type l1) → UU (lsuc lzero ⊔ l1)
symmetric-H-Space A =
  (X : 2-Element-Type lzero) → ℤ/2-action-H-Space A X

commutative-mul-symmetric-H-Space :
  {l1 : Level} (A : Pointed-Type l1) (μ : symmetric-H-Space A) →
  commutative-operation (type-Pointed-Type A) (type-Pointed-Type A)
commutative-mul-symmetric-H-Space A μ (X , f) = pr1 (μ X) f

module _
  {l1 : Level} (A : Pointed-Type l1) (X : 2-Element-Type lzero)
  where

  htpy-ℤ/2-action-H-space :
    (μ μ' : ℤ/2-action-H-Space A X) → UU {!!}
  htpy-ℤ/2-action-H-space μ μ' =
    Σ ( (f : type-2-Element-Type X → type-Pointed-Type A) → pr1 μ f ＝ pr1 μ' f)
      ( λ H →
        Σ ( ( f : type-2-Element-Type X → type-Pointed-Type A) →
            ( x : type-2-Element-Type X) →
            ( p : f x ＝ pt-Pointed-Type A) →
            pr1 (pr2 μ) f x p ＝ (H f ∙ pr1 (pr2 μ') f x p))
          ( λ K →
            Eq-symmetric-Id (X , (λ x → pr1 (pr2 μ') (const _ _ (pt-Pointed-Type A)) x refl)) {!pr2 (pr2 μ)!} (pr2 (pr2 μ'))))
```
