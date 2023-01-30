---
title: Propositions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.propositions where

open import foundation-core.propositions public

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using (is-equiv-has-inverse; _≃_)
open import foundation-core.function-extensionality using
  ( htpy-eq; equiv-funext)
open import foundation-core.functions using (id; _∘_)
open import foundation-core.homotopies using (_~_; refl-htpy)
open import foundation-core.truncated-types using
  ( is-trunc)
open import foundation-core.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; succ-𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.contractible-types using
  ( is-contr; is-trunc-is-contr; eq-is-contr; is-contr-equiv;
    is-prop-is-contr; is-property-is-contr)
```

### Propositions are (k+1)-truncated for any k.

```agda
abstract
  is-trunc-is-prop :
    { l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)
```
