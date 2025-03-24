# Transitive multisets

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module trees.transitive-multisets
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import trees.multisets funext univalence truncations
open import trees.submultisets funext univalence truncations
```

</details>

## Idea

A multiset `x` is said to be **transitive** if `y ⊑-𝕍 x` for every `y ∈-𝕍 x`.
That is, `x` is transitive if for every `z ∈-𝕍 y ∈-𝕍 x` we have
`z ∈-𝕍 y ≃ z ∈-𝕍 x`.

Similarly, we say that `x` is **weakly transitive** if `y ⊆-𝕍 x` for every
`y ∈-𝕍 x`. That is, `x` is weakly transitive if for every `z ∈-𝕍 y ∈-𝕍 x` we
have `z ∈-𝕍 y ↪ z ∈-𝕍 x`.

## Definition

### Transitive multisets

```agda
is-transitive-𝕍 : {l : Level} → 𝕍 l → UU (lsuc l)
is-transitive-𝕍 {l} x = (y : 𝕍 l) → y ∈-𝕍 x → y ⊑-𝕍 x
```

### Wealky transitive multisets

```agda
is-weakly-transitive-𝕍 : {l : Level} → 𝕍 l → UU (lsuc l)
is-weakly-transitive-𝕍 {l} x = (y : 𝕍 l) → y ∈-𝕍 x → y ⊆-𝕍 x
```
