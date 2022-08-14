---
title: Connected components of types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.connected-components where

open import foundation.0-connected-types using
  ( is-0-connected; is-0-connected-mere-eq)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.identity-types using (_＝_; refl; inv)
open import foundation.propositional-truncations using
  ( trunc-Prop; type-trunc-Prop; unit-trunc-Prop; apply-universal-property-trunc-Prop;
    all-elements-equal-type-trunc-Prop; is-prop-type-trunc-Prop)
open import foundation.propositions using (is-trunc-is-prop)
open import foundation.truncated-types using (is-trunc; is-trunc-Σ)
open import foundation.truncation-levels using (𝕋; succ-𝕋)
open import foundation.universe-levels using (UU; Level)

open import group-theory.higher-groups using (∞-Group)

open import structured-types.pointed-types using (Pointed-Type)
```

## Idea

The connected component of a type `A` at an element `a : A` is the type of all `x : A` that are merely equal to `a`.

## Definition

```agda
module _
  {l : Level} (A : UU l) (a : A)
  where

  connected-component : UU l
  connected-component =
    Σ A (λ x → type-trunc-Prop (x ＝ a))

  point-connected-component : connected-component
  pr1 point-connected-component = a
  pr2 point-connected-component = unit-trunc-Prop refl

  connected-component-Pointed-Type : Pointed-Type l
  pr1 connected-component-Pointed-Type = connected-component
  pr2 connected-component-Pointed-Type = point-connected-component

  value-connected-component :
    connected-component → A
  value-connected-component X = pr1 X

  abstract
    mere-equality-connected-component : (X : connected-component) →
      type-trunc-Prop (value-connected-component X ＝ a)
    mere-equality-connected-component X = pr2 X
```

## Properties

### Connected components are 0-connected

```agda
abstract
  is-0-connected-connected-component :
    {l : Level} (A : UU l) (a : A) →
    is-0-connected (connected-component A a)
  is-0-connected-connected-component A a =
    is-0-connected-mere-eq
      ( pair a (unit-trunc-Prop refl))
      ( λ (pair x p) →
        apply-universal-property-trunc-Prop
          ( p)
          ( trunc-Prop (pair a (unit-trunc-Prop refl) ＝ pair x p))
          ( λ p' →
            unit-trunc-Prop
              ( eq-pair-Σ
                ( inv p')
                ( all-elements-equal-type-trunc-Prop _ p))))

connected-component-∞-Group :
  {l : Level} (A : UU l) (a : A) → ∞-Group l
pr1 (connected-component-∞-Group A a) = connected-component-Pointed-Type A a
pr2 (connected-component-∞-Group A a) = is-0-connected-connected-component A a
```

### If `A` is (k+1)-truncated, then the connected component of `a` in `A` is (k+1)-truncated.

```agda
is-trunc-connected-component :
  {l : Level} {k : 𝕋} (A : UU l) (a : A) →
  is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (connected-component A a)
is-trunc-connected-component {l} {k} A a H =
  is-trunc-Σ H (λ x → is-trunc-is-prop k is-prop-type-trunc-Prop)

```

