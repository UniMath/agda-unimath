# Functions

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.functions where

open import foundation.universe-levels using (Level; UU)
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

### Evaluating at a point
```agda
ev-pt :
  {l1 l2 : Level} {A : UU l1} (a : A) (B : A → UU l2) → ((x : A) → B x) → B a
ev-pt a B f = f a
```

### Swapping the order of two variables

```agda
Π-swap : {i j k : Level} {A : UU i} {B : UU j} {C : A → (B → UU k)} →
  ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
Π-swap f y x = f x y
```
