# Finite reindexings of coverings in locales

```agda
module order-theory.finite-reindexing-covering-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import order-theory.coverings-locales
open import order-theory.finite-coverings-locales
open import order-theory.locales
open import order-theory.reindexing-covering-locales

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **finite reindexing** of a [covering](order-theory.coverings-locales.md) in a
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

  is-finite-reindexing-covering-Locale :
    (r : reindexing-covering-Locale L v) → UU l2
  is-finite-reindexing-covering-Locale r =
    is-finite (domain-reindexing-covering-Locale L v r)

  finite-reindexing-covering-Locale : UU (l1 ⊔ lsuc l2)
  finite-reindexing-covering-Locale =
    Σ (𝔽 l2)
      ( λ J →
        Σ ( type-𝔽 J → indexing-type-covering-Locale L v)
          ( is-reindexing-covering-Locale L v))

module _
  {l1 l2 : Level} (L : Locale l1 l2) {u : type-Locale L}
  (v : covering-Locale L u) (r : finite-reindexing-covering-Locale L v)
  where

  domain-finite-reindexing-covering-Locale : UU l2
  domain-finite-reindexing-covering-Locale = type-𝔽 (pr1 r)

  reindexing-map-finite-reindexing-covering-Locale :
    domain-finite-reindexing-covering-Locale →
    indexing-type-covering-Locale L v
  reindexing-map-finite-reindexing-covering-Locale = pr1 (pr2 r)

  covering-family-finite-reindexing-covering-Locale :
    domain-finite-reindexing-covering-Locale → type-Locale L
  covering-family-finite-reindexing-covering-Locale =
    (covering-family-covering-Locale L v) ∘
    (reindexing-map-finite-reindexing-covering-Locale)

  is-reindexing-finite-reindexing-covering-Locale :
    is-reindexing-covering-Locale L v
      ( reindexing-map-finite-reindexing-covering-Locale)
  is-reindexing-finite-reindexing-covering-Locale = pr2 (pr2 r)

  reindexing-finite-reindexing-covering-Locale :
    reindexing-covering-Locale L v
  pr1 reindexing-finite-reindexing-covering-Locale =
    domain-finite-reindexing-covering-Locale
  pr1 (pr2 reindexing-finite-reindexing-covering-Locale) =
    reindexing-map-finite-reindexing-covering-Locale
  pr2 (pr2 reindexing-finite-reindexing-covering-Locale) =
    is-reindexing-finite-reindexing-covering-Locale

  is-finite-reindexing-finite-reindexing-covering-Locale :
    is-finite-reindexing-covering-Locale L v
      ( reindexing-finite-reindexing-covering-Locale)
  is-finite-reindexing-finite-reindexing-covering-Locale =
    is-finite-type-𝔽 (pr1 r)
```
