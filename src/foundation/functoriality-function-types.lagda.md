# Functoriality of function types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.functoriality-function-types where

open import foundation-core.functoriality-function-types public

open import foundation.constant-maps using (const)
open import foundation.contractible-types using (center; eq-is-contr')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (postcomp; id; _∘_)
open import foundation.function-extensionality using (htpy-eq; eq-htpy)
open import foundation.functoriality-dependent-function-types using
  ( is-trunc-map-map-Π-is-trunc-map';
    is-trunc-map-is-trunc-map-map-Π')
open import foundation.homotopies using (htpy-right-whisk)
open import foundation.identity-types using (ap; refl)
open import foundation.truncation-levels using (𝕋; neg-two-𝕋)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU)

open import foundation-core.contractible-maps using
  ( is-equiv-is-contr-map; is-contr-map-is-equiv)
open import foundation-core.equivalences using
  ( is-equiv; is-equiv-has-inverse; map-inv-is-equiv; issec-map-inv-is-equiv;
    isretr-map-inv-is-equiv; _≃_; map-equiv; is-equiv-map-equiv)
open import foundation-core.truncated-maps using (is-trunc-map)
```

## Properties

```agda
is-trunc-map-postcomp-is-trunc-map :
  {l1 l2 l3 : Level} (k : 𝕋) (A : UU l3) {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-trunc-map k f → is-trunc-map k (postcomp A f)
is-trunc-map-postcomp-is-trunc-map k A {X} {Y} f is-trunc-f =
  is-trunc-map-map-Π-is-trunc-map' k
    ( const A unit star)
    ( const unit (X → Y) f)
    ( const unit (is-trunc-map k f) is-trunc-f)

is-trunc-map-is-trunc-map-postcomp :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {Y : UU l2} (f : X → Y) →
  ( {l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)) →
  is-trunc-map k f
is-trunc-map-is-trunc-map-postcomp k {X} {Y} f is-trunc-post-f =
  is-trunc-map-is-trunc-map-map-Π' k
    ( const unit (X → Y) f)
    ( λ {l} {J} α → is-trunc-post-f {l} J)
    ( star)
```
