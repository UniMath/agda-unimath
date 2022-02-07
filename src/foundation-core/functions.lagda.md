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

### Evaluating at a point

```agda
ev-pt :
  {l1 l2 : Level} {A : UU l1} (a : A) (B : A → UU l2) → ((x : A) → B x) → B a
ev-pt a B f = f a
```

### Precomposition

```agda
precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ((b : B) → C b) → ((a : A) → C (f a))
precomp-Π f C h a = h (f a)

precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (B → C) → (A → C)
precomp f C = precomp-Π f (λ b → C)
```
