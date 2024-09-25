# Equivalences between synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.equivalences-synthetic-categories where
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

A functor f: A → B of
[synthetic categories](synthetic-category-theory.synthetic-categories.md) is an
{{#concept "equivalence" Disambiguation="Synthetic categories}} if it has a
[section](synthetic-category-theory.sections-synthetic-categories.md) and a
[retraction](synthetic-category-theory.retractions-synthetic-categories.md).

### The predicate of being an equivalence

```agda
module _
  {l : Level}
  where

  is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (f : functor-Synthetic-Category-Theory κ C D) → UU l
  is-equiv-Synthetic-Category-Theory κ μ ι f =
    ( section-Synthetic-Category-Theory κ μ ι f)
      ×
    ( retraction-Synthetic-Category-Theory κ μ ι f)
```

### The components of a proof of being an equivalence

```agda
module _
  {l : Level}
  where

  section-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-equiv-Synthetic-Category-Theory κ μ ι f →
    section-Synthetic-Category-Theory κ μ ι f
  section-is-equiv-Synthetic-Category-Theory κ μ ι = pr1

  retraction-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-equiv-Synthetic-Category-Theory κ μ ι f →
    retraction-Synthetic-Category-Theory κ μ ι f
  retraction-is-equiv-Synthetic-Category-Theory κ μ ι = pr2
```

### The type of equivalences between two given synthetic categories

```agda
module _
  {l : Level}
  where

  equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (C D : category-Synthetic-Category-Theory κ) → UU l
  equiv-Synthetic-Category-Theory κ μ ι C D =
    Σ ( functor-Synthetic-Category-Theory κ C D)
      ( is-equiv-Synthetic-Category-Theory κ μ ι)
```

### The components of an equivalence of synthetic categories

```agda
module _
  {l : Level}
  where

  functor-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ) →
    equiv-Synthetic-Category-Theory κ μ ι C D →
    functor-Synthetic-Category-Theory κ C D
  functor-equiv-Synthetic-Category-Theory κ μ ι = pr1

  is-equiv-functor-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ) →
    (H : equiv-Synthetic-Category-Theory κ μ ι C D) →
    is-equiv-Synthetic-Category-Theory κ μ ι
      ( functor-equiv-Synthetic-Category-Theory κ μ ι H)
  is-equiv-functor-equiv-Synthetic-Category-Theory κ μ ι = pr2

  section-functor-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (H : equiv-Synthetic-Category-Theory κ μ ι C D) →
    section-Synthetic-Category-Theory κ μ ι
      ( functor-equiv-Synthetic-Category-Theory κ μ ι H)
  section-functor-equiv-Synthetic-Category-Theory κ μ ι H =
    section-is-equiv-Synthetic-Category-Theory κ μ ι
      ( is-equiv-functor-equiv-Synthetic-Category-Theory κ μ ι H)

  functor-section-functor-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (H : equiv-Synthetic-Category-Theory κ μ ι C D) →
    functor-Synthetic-Category-Theory κ D C
  functor-section-functor-equiv-Synthetic-Category-Theory κ μ ι H =
    functor-section-Synthetic-Category-Theory κ μ ι
      ( section-functor-equiv-Synthetic-Category-Theory κ μ ι H)

  retraction-functor-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (H : equiv-Synthetic-Category-Theory κ μ ι C D) →
    retraction-Synthetic-Category-Theory κ μ ι
      ( functor-equiv-Synthetic-Category-Theory κ μ ι H)
  retraction-functor-equiv-Synthetic-Category-Theory κ μ ι H =
    retraction-is-equiv-Synthetic-Category-Theory κ μ ι
      ( is-equiv-functor-equiv-Synthetic-Category-Theory κ μ ι H)

  functor-retraction-functor-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (H : equiv-Synthetic-Category-Theory κ μ ι C D) →
    functor-Synthetic-Category-Theory κ D C
  functor-retraction-functor-equiv-Synthetic-Category-Theory κ μ ι H =
    functor-retraction-Synthetic-Category-Theory κ μ ι
      ( retraction-functor-equiv-Synthetic-Category-Theory κ μ ι H)
```
