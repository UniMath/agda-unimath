# Cospans of synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.cospans-synthetic-categories where
```

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types

open import synthetic-category-theory.synthetic-categories
```

### Cospans of synthetic categories

A cospan is a pair of maps with a common codomain

```agda
module _
  {l : Level}
  where

  cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (C D E : category-Synthetic-Category-Theory κ ) → UU l
  cospan-Synthetic-Category-Theory κ C D E =
    Σ ( functor-Synthetic-Category-Theory κ C E)
      λ f → functor-Synthetic-Category-Theory κ D E

  left-source-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ} →
    cospan-Synthetic-Category-Theory κ C D E →
      category-Synthetic-Category-Theory κ
  left-source-cospan-Synthetic-Category-Theory κ {D = D} S = D

  right-source-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ} →
    cospan-Synthetic-Category-Theory κ C D E →
      category-Synthetic-Category-Theory κ
  right-source-cospan-Synthetic-Category-Theory κ {C = C} S = C

  target-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ} →
    cospan-Synthetic-Category-Theory κ C D E →
    category-Synthetic-Category-Theory κ
  target-cospan-Synthetic-Category-Theory κ {E = E} S = E

  left-map-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (S : cospan-Synthetic-Category-Theory κ C D E) →
    functor-Synthetic-Category-Theory κ
      ( left-source-cospan-Synthetic-Category-Theory κ S)
      ( target-cospan-Synthetic-Category-Theory κ S)
  left-map-cospan-Synthetic-Category-Theory κ S = pr2 S

  right-map-cospan-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (S : cospan-Synthetic-Category-Theory κ C D E) →
    functor-Synthetic-Category-Theory κ
      ( right-source-cospan-Synthetic-Category-Theory κ S)
      ( target-cospan-Synthetic-Category-Theory κ S)
  right-map-cospan-Synthetic-Category-Theory κ S = pr1 S
```
