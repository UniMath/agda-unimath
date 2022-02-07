# Subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.subtypes where

open import foundation-core.subtypes public

open import foundation-core.dependent-pair-types using (Σ)
open import foundation-core.truncation-levels using (𝕋; zero-𝕋)
open import foundation-core.universe-levels using (Level; UU)

open import foundation.1-types using (is-1-type)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  where

  abstract
    is-1-type-is-subtype : is-subtype P → is-1-type A → is-1-type (Σ A P)
    is-1-type-is-subtype = is-trunc-is-subtype zero-𝕋
```
