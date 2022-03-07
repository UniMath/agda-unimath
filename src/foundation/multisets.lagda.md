# Multisets

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.multisets where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.elementhood-relation-w-types using (_∈-𝕎_)
open import foundation.empty-types using (is-empty)
open import foundation.functions using (_∘_)
open import foundation.universe-levels using (Level; UU; lsuc)
open import foundation.w-types using (𝕎; symbol-𝕎; tree-𝕎; component-𝕎)
```

## Idea

The type of multisets of universe level `l` is the W-type of the universal family over the universe `UU l`.

## Definitions

### The type of multisets

```agda
𝕍 : (l : Level) → UU (lsuc l)
𝕍 l = 𝕎 (UU l) (λ X → X)
```

### The elementhood relation on multisets

```agda
_∈-𝕍_ : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
X ∈-𝕍 Y = X ∈-𝕎 Y

_∉-𝕍_ : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
X ∉-𝕍 Y = is-empty (X ∈-𝕍 Y)
```

### Comprehension for multisets

```agda
comprehension-𝕍 :
  {l : Level} (X : 𝕍 l) (P : symbol-𝕎 X → UU l) → 𝕍 l
comprehension-𝕍 X P =
  tree-𝕎 (Σ (symbol-𝕎 X) P) (component-𝕎 X ∘ pr1)
```
