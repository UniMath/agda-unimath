# Pullbacks of synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.pullbacks-synthetic-categories where
```

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types

open import synthetic-category-theory.synthetic-categories
open import synthetic-category-theory.cospans-synthetic-categories
open import synthetic-category-theory.cone-diagrams-synthetic-categories
```

### Pullbacks of synthetic categories

```agda
module _
  {l : Level}
  where

  record
    pullback-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
      {C D E : category-Synthetic-Category-Theory κ}
      (μ : composition-Synthetic-Category-Theory κ)
      (ι : identity-Synthetic-Category-Theory κ)
      (ν : inverse-Synthetic-Category-Theory κ μ ι)
      (Α : associative-composition-Synthetic-Category-Theory κ μ)
      (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
      (Λ : left-unit-law-composition-Synthetic-Category-Theory κ ι μ)
      (Ρ : right-unit-law-composition-Synthetic-Category-Theory κ ι μ)
      (Ξ : preserves-associativity-composition-horizontal-composition-Synthetic-Category-Theory κ μ Α Χ)
      (I : interchange-composition-Synthetic-Category-Theory κ μ Χ)
      (M : preserves-isomorphism-horizontal-composition-Synthetic-Category-Theory κ ι μ Χ)
      (N : preserves-identity-horizontal-composition-Synthetic-Category-Theory κ ι μ Χ)
      (S : cospan-Synthetic-Category-Theory κ C D E) : UU l
    where
    coinductive
    field
      apex-pullback-Synthetic-Category-Theory :
        category-Synthetic-Category-Theory κ
      cone-diagram-pullback-Synthetic-Category-Theory :
        cone-diagram-Synthetic-Category-Theory
          κ μ S apex-pullback-Synthetic-Category-Theory
      universality-functor-pullback-Synthetic-Category-Theory :
        (T : category-Synthetic-Category-Theory κ)
        (c : cone-diagram-Synthetic-Category-Theory κ μ S T) →
          functor-Synthetic-Category-Theory κ
            T apex-pullback-Synthetic-Category-Theory
      universality-iso-pullback-Synthetic-Category-Theory :
        (T : category-Synthetic-Category-Theory κ)
        (c : cone-diagram-Synthetic-Category-Theory κ μ S T) →
          iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ S T
            ( c)
            ( induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S
              apex-pullback-Synthetic-Category-Theory
              cone-diagram-pullback-Synthetic-Category-Theory
              ( T)
              ( universality-functor-pullback-Synthetic-Category-Theory T c))
      triviality-iso-of-cone-diagrams-pullback-Synthetic-Category-Theory :
        {T : category-Synthetic-Category-Theory κ}
        (s t : functor-Synthetic-Category-Theory κ T apex-pullback-Synthetic-Category-Theory)
        (H : iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ S T
          (induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S
            apex-pullback-Synthetic-Category-Theory
            cone-diagram-pullback-Synthetic-Category-Theory T s)
          (induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S
            apex-pullback-Synthetic-Category-Theory
            cone-diagram-pullback-Synthetic-Category-Theory T t)) →
          Σ ( isomorphism-Synthetic-Category-Theory κ s t)
            λ α →
              iso-of-isos-of-cone-diagrams-Synthetic-Category-Theory κ μ ι ν Χ M S T
                ( induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S
                  apex-pullback-Synthetic-Category-Theory
                  cone-diagram-pullback-Synthetic-Category-Theory
                  T s)
                ( induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S
                  apex-pullback-Synthetic-Category-Theory
                  cone-diagram-pullback-Synthetic-Category-Theory
                  T t)
                ( induced-iso-cone-diagram-Synthetic-Category-Theory
                  κ μ ι ν Α Χ Λ Ρ Ξ I M N S
                  apex-pullback-Synthetic-Category-Theory
                  cone-diagram-pullback-Synthetic-Category-Theory
                  T s t α)
                ( H)
```
