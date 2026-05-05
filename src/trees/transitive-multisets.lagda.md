# Transitive multisets

```agda
module trees.transitive-multisets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import trees.multisets
open import trees.submultisets
```

</details>

## Idea

A [multiset](trees.multisets.md) `x` is said to be
{{#concept "transitive" Disambiguation="multiset" Agda=is-transitive-𝕍}} if
`y ⊑-𝕍 x` for every `y ∈-𝕍 x`. That is, `x` is transitive if for every
`z ∈-𝕍 y ∈-𝕍 x` we have `z ∈-𝕍 y ≃ z ∈-𝕍 x`.

Similarly, we say that `x` is
{{#concept "weakly transitive" Disambiguation="multiset" Agda=is-weakly-transitive-𝕍}}
if `y ⊆-𝕍 x` for every `y ∈-𝕍 x`. That is, `x` is weakly transitive if for every
`z ∈-𝕍 y ∈-𝕍 x` we have `z ∈-𝕍 y ↪ z ∈-𝕍 x`.

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
