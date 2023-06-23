# Finite coverings in locales

```agda
module order-theory.finite-coverings-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
open import foundation.dependent-pair-types

open import order-theory.frames
open import order-theory.greatest-lower-bounds-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.meet-semilattices
open import order-theory.meet-suplattices
open import order-theory.posets
open import order-theory.suplattices
open import order-theory.locales
open import order-theory.coverings-locales

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **finite covering** of an object `u` in a locale is a finite family of objects
whose join is `u`.

## Definition

```agda
module _
  {l1 l2 : Level}(L : Locale l1 l2)(u : type-Locale L)
  where

  is-finite-covering-Locale : (v : covering-Locale L u) → UU l2
  is-finite-covering-Locale v = is-finite (indexing-type-covering-Locale L v)

  finite-covering-Locale : UU (l1 ⊔ lsuc l2)
  finite-covering-Locale =
    Σ ( 𝔽 l2)
      ( λ I →
        Σ ( type-𝔽 I → type-Locale L)
          ( is-covering-Locale L u) )

module _
  {l1 l2 : Level}(L : Locale l1 l2) {u : type-Locale L}
  (v : finite-covering-Locale L u)
  where

  indexing-type-finite-covering-Locale : UU l2
  indexing-type-finite-covering-Locale = type-𝔽 (pr1 v)

  covering-family-finite-covering-Locale :
    indexing-type-finite-covering-Locale → type-Locale L
  covering-family-finite-covering-Locale = pr1 (pr2 v)

  is-covering-finite-covering-Locale :
    is-covering-Locale L u covering-family-finite-covering-Locale
  is-covering-finite-covering-Locale = pr2 (pr2 v)

  covering-finite-covering-Locale : covering-Locale L u
  pr1 covering-finite-covering-Locale = indexing-type-finite-covering-Locale
  pr1 (pr2 covering-finite-covering-Locale) = covering-family-finite-covering-Locale
  pr2 (pr2 covering-finite-covering-Locale) = is-covering-finite-covering-Locale

  is-finite-covering-covering-Locale :
    is-finite-covering-Locale L u covering-finite-covering-Locale
  is-finite-covering-covering-Locale = is-finite-type-𝔽 (pr1 v)

```
