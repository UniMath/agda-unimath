# Truncated maps

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.truncated-maps where

open import foundation-core.truncated-maps public

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.fibers-of-maps using (fib)
open import foundation-core.truncation-levels using (𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.propositions using (is-prop; is-prop-Π; UU-Prop)
open import foundation.truncated-types using (is-prop-is-trunc)
```

## Properties

### Being a truncated map is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  is-prop-is-trunc-map : (k : 𝕋) (f : A → B) → is-prop (is-trunc-map k f)
  is-prop-is-trunc-map k f = is-prop-Π (λ x → is-prop-is-trunc k (fib f x))

  is-trunc-map-Prop : (k : 𝕋) → (A → B) → UU-Prop (l1 ⊔ l2)
  pr1 (is-trunc-map-Prop k f) = is-trunc-map k f
  pr2 (is-trunc-map-Prop k f) = is-prop-is-trunc-map k f
```
