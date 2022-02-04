# Functions

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation-core.functions where

open import foundation-core.universe-levels using (Level; UU)
```

## Idea

Functions are primitive in Agda. Here we construct some basic functions

## Examples

### The identity function

```agda
id : {i : Level} {A : UU i} → A → A
id a = a
```

### Dependent composition of functions

```agda
_∘_ :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : (a : A) → B a → UU k} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)
```
