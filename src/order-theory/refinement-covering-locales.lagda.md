# Refinement of coverings in locales

```agda
module order-theory.refinement-covering-locales where
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

A **refinement** of a [covering](order-theory.coverings-locales.md) in a
[locale](order-theory.locales.md) is a map into the indexing type of the
covering such that the composition still yields a covering of the same object.

## Definition

```agda
module _
  {l1 l2 : Level} {L : Locale l1 l2} {u : type-Locale L}
  (v : covering-Locale L u)
  where

  is-refinement-covering-Locale : {J : UU l2}
    (f : J → (indexing-type-covering-Locale L v)) → UU l1
  is-refinement-covering-Locale f =
    is-covering-Locale L u ((covering-family-covering-Locale L v) ∘ f)

  refinement-covering-Locale : UU (l1 ⊔ lsuc l2)
  refinement-covering-Locale =
    Σ (UU l2)
      ( λ J →
        Σ ( J → indexing-type-covering-Locale L v)
          ( is-refinement-covering-Locale ))

module _
  {l1 l2 : Level} {L : Locale l1 l2} {u : type-Locale L}
  {v : covering-Locale L u} (r : refinement-covering-Locale v)
  where

  domain-refinement-covering-Locale : UU l2
  domain-refinement-covering-Locale = pr1 r

```
