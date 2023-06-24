# Finite refinement of coverings in locales

```agda
module order-theory.finite-refinement-covering-locales where
```

<details><summary>Imports</summary>

```agda

open import foundation-core.function-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import order-theory.coverings-locales
open import order-theory.locales
open import order-theory.finite-coverings-locales
open import order-theory.refinement-covering-locales

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **finite refinement** of a [covering](order-theory.coverings-locales.md) in a
[locale](order-theory.locales.md) is a map from a
[finite type](univalent-combinatorics.finite-types.md) into the indexing type of
the covering such that the composition still yields a covering of the same
object.

## Definition

```agda
module _
  {l1 l2 : Level} (L : Locale l1 l2) {u : type-Locale L}
  (v : covering-Locale L u)
  where

  is-finite-refinement-covering-Locale :
    (r : refinement-covering-Locale L v) → UU l2
  is-finite-refinement-covering-Locale r =
    is-finite (domain-refinement-covering-Locale L v r)

  finite-refinement-covering-Locale : UU (l1 ⊔ lsuc l2)
  finite-refinement-covering-Locale =
    Σ (𝔽 l2)
      ( λ J →
        Σ ( type-𝔽 J → indexing-type-covering-Locale L v)
          ( is-refinement-covering-Locale L v))

module _
  {l1 l2 : Level} (L : Locale l1 l2) {u : type-Locale L}
  (v : covering-Locale L u) (r : finite-refinement-covering-Locale L v)
  where

  domain-finite-refinement-covering-Locale : UU l2
  domain-finite-refinement-covering-Locale = type-𝔽 (pr1 r)

  reindexing-finite-refinement-covering-Locale :
    domain-finite-refinement-covering-Locale →
    indexing-type-covering-Locale L v
  reindexing-finite-refinement-covering-Locale = pr1 (pr2 r)

  covering-family-finite-refinement-covering-Locale :
    domain-finite-refinement-covering-Locale → type-Locale L
  covering-family-finite-refinement-covering-Locale =
    (covering-family-covering-Locale L v) ∘
    (reindexing-finite-refinement-covering-Locale)

  is-refinement-finite-refinement-covering-Locale :
    is-refinement-covering-Locale L v
    reindexing-finite-refinement-covering-Locale
  is-refinement-finite-refinement-covering-Locale = pr2 (pr2 r)

  refinement-finite-refinement-covering-Locale :
    refinement-covering-Locale L v
  pr1 refinement-finite-refinement-covering-Locale =
    domain-finite-refinement-covering-Locale
  pr1 (pr2 refinement-finite-refinement-covering-Locale) =
    reindexing-finite-refinement-covering-Locale
  pr2 (pr2 refinement-finite-refinement-covering-Locale) =
    is-refinement-finite-refinement-covering-Locale

  is-finite-refinement-finite-refinement-covering-Locale :
    is-finite-refinement-covering-Locale L v
    refinement-finite-refinement-covering-Locale
  is-finite-refinement-finite-refinement-covering-Locale =
    is-finite-type-𝔽 (pr1 r)

```
