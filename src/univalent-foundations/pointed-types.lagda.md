# Pointed types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-foundations.pointed-types where

open import univalent-foundations.17-univalence public

-- The universe of pointed types

Pointed-Type : (l : Level) → UU (lsuc l)
Pointed-Type l = Σ (UU l) (λ X → X)

module _
  {l : Level} (A : Pointed-Type l)
  where
  
  type-Pointed-Type : UU l
  type-Pointed-Type = pr1 A
  
  pt-Pointed-Type : type-Pointed-Type
  pt-Pointed-Type = pr2 A
```
