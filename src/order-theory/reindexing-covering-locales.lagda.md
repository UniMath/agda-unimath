# Reindexings of coverings in locales

```agda
module order-theory.reindexing-covering-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import order-theory.coverings-locales
open import order-theory.finite-coverings-locales
open import order-theory.locales

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **reindexing** of a [covering](order-theory.coverings-locales.md) in a
[locale](order-theory.locales.md) is a map into the indexing type of the
covering such that the restriction of the original covering along this map still
yields a covering of the same object.

## Definition

```agda
module _
  {l1 l2 : Level} (L : Locale l1 l2) {u : type-Locale L}
  (v : covering-Locale L u)
  where

  is-reindexing-covering-Locale : {J : UU l2}
    (f : J → (indexing-type-covering-Locale L v)) → UU l1
  is-reindexing-covering-Locale f =
    is-covering-Locale L u ((covering-family-covering-Locale L v) ∘ f)

  reindexing-covering-Locale : UU (l1 ⊔ lsuc l2)
  reindexing-covering-Locale =
    Σ (UU l2)
      ( λ J →
        Σ ( J → indexing-type-covering-Locale L v)
          ( is-reindexing-covering-Locale))

module _
  {l1 l2 : Level} (L : Locale l1 l2) {u : type-Locale L}
  (v : covering-Locale L u) (r : reindexing-covering-Locale L v)
  where

  domain-reindexing-covering-Locale : UU l2
  domain-reindexing-covering-Locale = pr1 r

  reindexing-map-reindexing-covering-Locale :
    domain-reindexing-covering-Locale → indexing-type-covering-Locale L v
  reindexing-map-reindexing-covering-Locale = pr1 (pr2 r)

  covering-family-reindexing-covering-Locale :
    domain-reindexing-covering-Locale → type-Locale L
  covering-family-reindexing-covering-Locale =
    (covering-family-covering-Locale L v) ∘
    (reindexing-map-reindexing-covering-Locale)

  is-covering-reindexing-covering-Locale :
    is-covering-Locale L u covering-family-reindexing-covering-Locale
  is-covering-reindexing-covering-Locale = pr2 (pr2 r)
```
