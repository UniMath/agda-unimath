# Truncated types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.truncated-types where

open import foundation-core.truncated-types public

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.embeddings using
  ( is-emb; _↪_; map-emb; is-emb-map-emb)
open import foundation-core.equality-cartesian-product-types using
  ( Eq-prod; equiv-pair-eq)
open import foundation-core.equality-dependent-pair-types using
  ( equiv-pair-eq-Σ)
open import foundation-core.homotopies using (_~_)
open import foundation-core.identity-types using (Id; refl; ap; tr)
open import foundation-core.propositions using (is-prop)
open import foundation-core.retractions using (_retract-of_)
open import foundation-core.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; succ-𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.contractible-types using
  ( is-contr-Σ'; is-contr-left-factor-prod; is-contr-right-factor-prod;
    is-contr-Π; is-subtype-is-contr; is-contr-equiv-is-contr)
open import foundation.equivalences using
  ( _≃_; map-equiv; htpy-equiv; extensionality-equiv)
open import foundation.function-extensionality using (htpy-eq; funext)
```
