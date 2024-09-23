# Biinvertible maps between synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.biinvertible-maps-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types

open import synthetic-category-theory.retractions-synthetic-categories
open import synthetic-category-theory.sections-synthetic-categories
open import synthetic-category-theory.synthetic-categories
```

</details>

## Idea

A functor f: A → B is biinvertible if it has a section and a retraction. Note
that in this library, biinvertible maps are usually called equivalences.

### The predicate of being biinvertible

```agda
module _
  {l : Level}
  where

  is-biinv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (f : functor-Synthetic-Category-Theory κ C D) → UU l
  is-biinv-Synthetic-Category-Theory κ μ ι f =
    ( section-Synthetic-Category-Theory κ μ ι f)
      ×
    ( retraction-Synthetic-Category-Theory κ μ ι f)
```

### The components of a proof of biinvertibility

```agda
module _
  {l : Level}
  where

  section-is-biinv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-biinv-Synthetic-Category-Theory κ μ ι f →
      section-Synthetic-Category-Theory κ μ ι f
  section-is-biinv-Synthetic-Category-Theory κ μ ι = pr1

  retraction-is-biinv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-biinv-Synthetic-Category-Theory κ μ ι f →
      retraction-Synthetic-Category-Theory κ μ ι f
  retraction-is-biinv-Synthetic-Category-Theory κ μ ι = pr2
```

### The type of biinvertible functors

```agda
module _
  {l : Level}
  where

  biinv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (C D : category-Synthetic-Category-Theory κ) → UU l
  biinv-Synthetic-Category-Theory κ μ ι C D =
    Σ ( functor-Synthetic-Category-Theory κ C D)
      ( is-biinv-Synthetic-Category-Theory κ μ ι)
```

### The components of a biinvertible functor

```agda
module _
  {l : Level}
  where

  map-biinv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ) →
    biinv-Synthetic-Category-Theory κ μ ι C D →
      functor-Synthetic-Category-Theory κ C D
  map-biinv-Synthetic-Category-Theory κ μ ι = pr1

  is-biinv-map-biinv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ) →
    (H : biinv-Synthetic-Category-Theory κ μ ι C D) →
      is-biinv-Synthetic-Category-Theory κ μ ι
        ( map-biinv-Synthetic-Category-Theory κ μ ι H)
  is-biinv-map-biinv-Synthetic-Category-Theory κ μ ι = pr2

  section-map-biinv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (H : biinv-Synthetic-Category-Theory κ μ ι C D) →
      section-Synthetic-Category-Theory κ μ ι
        ( map-biinv-Synthetic-Category-Theory κ μ ι H)
  section-map-biinv-Synthetic-Category-Theory κ μ ι H =
    section-is-biinv-Synthetic-Category-Theory κ μ ι
      ( is-biinv-map-biinv-Synthetic-Category-Theory κ μ ι H)

  retraction-map-biinv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (H : biinv-Synthetic-Category-Theory κ μ ι C D) →
      retraction-Synthetic-Category-Theory κ μ ι
        ( map-biinv-Synthetic-Category-Theory κ μ ι H)
  retraction-map-biinv-Synthetic-Category-Theory κ μ ι H =
    retraction-is-biinv-Synthetic-Category-Theory κ μ ι
      ( is-biinv-map-biinv-Synthetic-Category-Theory κ μ ι H)
```
