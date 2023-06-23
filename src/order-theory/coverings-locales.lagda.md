# Coverings in locales

```agda
module order-theory.coverings-locales where
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
```

</details>

## Idea

A **covering** of an object `u` in a locale is a family of objects whose join is
`u`.

## Definition

```agda
module _
  {l1 l2 : Level}(L : Locale l1 l2)(u : type-Locale L)
  where

  is-covering-Locale :  {I : UU l2} → (I → type-Locale L) → UU l1
  is-covering-Locale x = (u ＝ sup-Locale L x)

  covering-Locale : UU (l1 ⊔ lsuc l2)
  covering-Locale =
    Σ ( UU l2)
      ( λ I →
        Σ ( I → type-Locale L)
          ( is-covering-Locale) )

module _
  {l1 l2 : Level}(L : Locale l1 l2) {u : type-Locale L} (v : covering-Locale L u)
  where

  indexing-type-covering-Locale : UU l2
  indexing-type-covering-Locale = pr1 v

  covering-family-covering-Locale : indexing-type-covering-Locale → type-Locale L
  covering-family-covering-Locale = pr1 (pr2 v)

  is-covering-covering-Locale :
    is-covering-Locale L u covering-family-covering-Locale
  is-covering-covering-Locale = pr2 (pr2 v)
```
