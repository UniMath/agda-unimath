# Quasicompact objects in locales

```agda
module order-theory.quasicompact-objects-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import order-theory.coverings-locales
open import order-theory.finite-coverings-locales
open import order-theory.finite-reindexing-covering-locales
open import order-theory.locales

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **quasicompact object** in a [locale](order-theory.locales.md) is one for
which every [covering](order-theory.coverings-locales.md) has a
[finite reindexing](order-theory.finite-reindexing-covering-locales.md).

## Definition

```agda
module _
  {l1 l2 : Level} (L : Locale l1 l2)
  where

  is-quasicompact-object-Locale : (u : type-Locale L) → UU (l1 ⊔ lsuc l2)
  is-quasicompact-object-Locale u = (v : covering-Locale L u) →
    finite-reindexing-covering-Locale L v

  quasicompact-objects-Locale : UU (l1 ⊔ lsuc l2)
  quasicompact-objects-Locale = Σ (type-Locale L) is-quasicompact-object-Locale
```
