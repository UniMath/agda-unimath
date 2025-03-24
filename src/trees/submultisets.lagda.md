# Submultisets

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module trees.submultisets
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddings funext
open import foundation.equivalences funext
open import foundation.universe-levels

open import trees.multisets funext univalence truncations
```

</details>

## Idea

Given two multisets `x` and `y`, we say that `x` is a **submultiset** of `y` if
for every `z ∈-𝕍 x` we have `z ∈-𝕍 x ↪ z ∈-𝕍 y`.

## Definition

### Submultisets

```agda
is-submultiset-𝕍 : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
is-submultiset-𝕍 {l} y x = (z : 𝕍 l) → z ∈-𝕍 x → (z ∈-𝕍 x) ↪ (z ∈-𝕍 y)

infix 6 _⊆-𝕍_
_⊆-𝕍_ : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
x ⊆-𝕍 y = is-submultiset-𝕍 y x
```

### Full submultisets

```agda
is-full-submultiset-𝕍 : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
is-full-submultiset-𝕍 {l} y x = (z : 𝕍 l) → z ∈-𝕍 x → (z ∈-𝕍 x) ≃ (z ∈-𝕍 y)

_⊑-𝕍_ : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
x ⊑-𝕍 y = is-full-submultiset-𝕍 y x
```
