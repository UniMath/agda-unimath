# Functions

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.functions where

open import foundation-core.functions public

open import foundation.universe-levels using (Level; UU)
```

## Idea

Functions are primitive in Agda. Here we construct some basic functions

### Swapping the order of two variables

```agda
Π-swap : {i j k : Level} {A : UU i} {B : UU j} {C : A → (B → UU k)} →
  ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
Π-swap f y x = f x y
```
