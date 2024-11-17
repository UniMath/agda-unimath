# Sections of functor between synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.sections-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.globular-types

open import synthetic-category-theory.synthetic-categories
```

</details>

## Idea

A section of a functor f: A → B is a functor g: B → A equipped with a natural
isomorphism f∘g ≅ id.

### The predicate of being a section of a functor f: A → B

```agda
module _
  {l : Level}
  where

  is-section-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (f : functor-Synthetic-Category-Theory κ C D) →
    functor-Synthetic-Category-Theory κ D C → UU l
  is-section-Synthetic-Category-Theory κ μ ι f s =
    isomorphism-Synthetic-Category-Theory κ
      ( comp-functor-Synthetic-Category-Theory μ f s)
      ( id-functor-Synthetic-Category-Theory ι _)
```

### The type of sections of a funcor f: A → B

```agda
module _
  {l : Level}
  where

  section-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (f : functor-Synthetic-Category-Theory κ C D) → UU l
  section-Synthetic-Category-Theory κ μ ι f =
    Σ ( functor-Synthetic-Category-Theory κ _ _)
      ( is-section-Synthetic-Category-Theory κ μ ι f)
```

### The components of a section

```agda
  functor-section-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    section-Synthetic-Category-Theory κ μ ι f →
      functor-Synthetic-Category-Theory κ D C
  functor-section-Synthetic-Category-Theory κ μ ι = pr1

  is-section-functor-section-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (s : section-Synthetic-Category-Theory κ μ ι f) →
      is-section-Synthetic-Category-Theory κ μ ι f
        ( functor-section-Synthetic-Category-Theory κ μ ι s)
  is-section-functor-section-Synthetic-Category-Theory κ μ ι = pr2
```
