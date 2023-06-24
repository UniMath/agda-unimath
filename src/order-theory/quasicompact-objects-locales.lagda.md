# Quasicompact objects in locales

```agda
module order-theory.quasicompact-objects-locales where
```

<details><summary>Imports</summary>

```agda

open import foundation-core.function-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import order-theory.coverings-locales
open import order-theory.locales
open import order-theory.finite-coverings-locales

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **quasicompact object** in a [locale](order-theory.locales.md) is one for
which every [covering](order-theory.coverings-locales.md) can be refined by a
[finite covering](order-theory.finite-coverings-locales).

## Definition

```agda
module _
  {l1 l2 : Level} (L : Locale l1 l2) (u : type-Locale L)
  where



  -- is-quasicompact-Locale : UU l2
  -- is-quasicompact-Locale =
  --   ( v : covering-Locale L u ) →
  --   Σ ( Σ (𝔽 l2) (λ J → (type-𝔽 J → ( indexing-type-covering-Locale L u v ))))
  --   ( λ J f → is-finite-covering-Locale L u (v ∘ f))

```
