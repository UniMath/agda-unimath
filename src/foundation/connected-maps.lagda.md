---
title: Connected maps
---

```agda
module foundation.connected-maps where

open import elementary-number-theory.natural-numbers

open import foundation.connected-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels
```

## Idea

A map is said to be **`k`-connected** if its fibers are `k`-connected types.

## Definition

```agda
is-connected-map-Prop :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
is-connected-map-Prop k {B = B} f =
  Π-Prop B (λ b → is-connected-Prop k (fib f b))

is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-connected-map k f = type-Prop (is-connected-map-Prop k f)

is-prop-is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-connected-map k f)
is-prop-is-connected-map k f = is-prop-type-Prop (is-connected-map-Prop k f)
```

## Properties

### Dependent universal property for connected maps

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B}
  where
  
  dependent-universal-property-is-connected-map :
    is-connected-map k f → (P : B → Truncated-Type l3 k) →
    is-equiv (precomp-Π f (λ b → type-Truncated-Type (P b)))
  dependent-universal-property-is-connected-map H P =
    is-equiv-precomp-Π-fiber-condition
      ( λ b → is-equiv-diagonal-is-connected (P b) (H b))
```

### A map `f : A → B` is `k`-connected if and only if precomposing dependent functions into `k + n`-truncated types is an `n-2`-truncated map for all `n : ℕ`

```agda
is-trunc-map-precomp-Π-is-connected-map :
  {l1 l2 l3 : Level} (k l n : 𝕋) → add-𝕋 k (succ-𝕋 (succ-𝕋 n)) ＝ l →
  {A : UU l1} {B : UU l2} {f : A → B} → is-connected-map k f →
  (P : B → Truncated-Type l3 l) →
  is-trunc-map
    ( n)
    ( precomp-Π f (λ b → type-Truncated-Type (P b)))
is-trunc-map-precomp-Π-is-connected-map
  {l1} {l2} {l3} k ._ neg-two-𝕋 refl {A} {B} H P =
  is-contr-map-is-equiv
    ( dependent-universal-property-is-connected-map k H
      ( λ b →
        pair
          ( type-Truncated-Type (P b))
          ( is-trunc-eq
            ( right-unit-law-add-𝕋 k)
            ( is-trunc-type-Truncated-Type (P b)))))
is-trunc-map-precomp-Π-is-connected-map k ._ (succ-𝕋 n) refl {A} {B} {f} H P =
  is-trunc-map-succ-precomp-Π
    ( λ g h →
      is-trunc-map-precomp-Π-is-connected-map k _ n refl H
        ( λ b →
          pair
            ( eq-value g h b)
            ( is-trunc-eq
              ( right-successor-law-add-𝕋 k n)
              ( is-trunc-type-Truncated-Type (P b))
              ( g b)
              ( h b))))
```
