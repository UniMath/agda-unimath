---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.laws-for-operations where

open import foundations.identity-types using (Id; _∙_; inv; ap)
open import foundations.levels using (UU; Level)
```

## Specifications of laws for operations

```agda
module _
  {l : Level} {X : UU l} (μ : X → X → X)
  where
  
  interchange-law : (X → X → X) → UU l
  interchange-law ν = (x y u v : X) → Id (μ (ν x y) (ν u v)) (ν (μ x u) (μ y v))

  interchange-law-commutative-and-associative :
    ((x y : X) → Id (μ x y) (μ y x)) →
    ((x y z : X ) → Id (μ (μ x y) z) (μ x (μ y z))) →
    interchange-law μ
  interchange-law-commutative-and-associative C A x y u v =
    ( A x y (μ u v)) ∙
    ( ( ap
        ( μ x)
        ( (inv (A y u v)) ∙ ((ap (λ z → μ z v) (C y u)) ∙ (A u y v)))) ∙
      ( inv (A x u (μ y v))))
```
