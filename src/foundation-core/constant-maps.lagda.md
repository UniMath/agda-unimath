# Constant maps

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.constant-maps where

open import foundation-core.universe-levels using (Level; UU)
```

## Definition

```agda
const : {i j : Level} (A : UU i) (B : UU j) (b : B) → A → B
const A B b x = b
```
