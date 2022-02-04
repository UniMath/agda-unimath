# Dependent pair types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation-core.dependent-pair-types where

open import foundation-core.universe-levels using (UU; Level; _⊔_)
```

## Idea

When `B` is a family of types over `A`, then we can form the type of pairs `pair a b` consisting of an element `a : A` and an element `b : B a`. Such pairs are called dependent pairs, since the type of the second component depends on the first component. 

## Definition

```agda
record Σ {l1 l2} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1

open Σ public

{-# BUILTIN SIGMA Σ #-}
```
