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
    is-finite (domain-refinement-covering-Locale L r)

```
