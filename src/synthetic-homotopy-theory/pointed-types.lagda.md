# Pointed types

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.pointed-types where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (Level; UU; lsuc)
```

## Idea

A pointed type is a type `A` equipped with an element `a : A`.

## Definition

### The universe of pointed types

```agda
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
