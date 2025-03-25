# Retractions of functors between synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.retractions-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import synthetic-category-theory.synthetic-categories
```

</details>

## Idea

A retraction of a functor f: A → B is a functor g: B → A equipped with a natural
isomorphism g∘f ≅ id.

### The predicate of being a retraction of a functor f: A → B

```agda
module _
  {l : Level}
  where

  is-retraction-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (f : functor-Synthetic-Category-Theory κ C D) →
    functor-Synthetic-Category-Theory κ D C → UU l
  is-retraction-Synthetic-Category-Theory κ μ ι f r =
    isomorphism-Synthetic-Category-Theory κ
      ( comp-functor-Synthetic-Category-Theory μ r f)
      ( id-functor-Synthetic-Category-Theory ι _)
```

### The type of retractions of a functor f: A → B

```agda
module _
  {l : Level}
  where

  retraction-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (f : functor-Synthetic-Category-Theory κ C D) → UU l
  retraction-Synthetic-Category-Theory κ μ ι f =
    Σ ( functor-Synthetic-Category-Theory κ _ _)
      ( is-retraction-Synthetic-Category-Theory κ μ ι f)
```

### The components of a retraction

```agda
  functor-retraction-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    retraction-Synthetic-Category-Theory κ μ ι f →
      functor-Synthetic-Category-Theory κ D C
  functor-retraction-Synthetic-Category-Theory κ μ ι = pr1

  is-retraction-functor-retraction-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (r : retraction-Synthetic-Category-Theory κ μ ι f) →
      is-retraction-Synthetic-Category-Theory κ μ ι f
        ( functor-retraction-Synthetic-Category-Theory κ μ ι r)
  is-retraction-functor-retraction-Synthetic-Category-Theory κ μ ι = pr2
```
