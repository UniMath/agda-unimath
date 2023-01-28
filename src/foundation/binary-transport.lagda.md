---
title: Binary transport
---

```agda
module foundation.binary-transport where

open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels
```

## Idea

Given a binary relation `B : A → A → UU` and identifications `p : x ＝ x'` and `q : y ＝ y'` in `A`, the binary transport of `B` is an operation

```md
  binary-tr B p q : B x y → B x' y'
```

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → A → UU l2)
  where
  
  binary-tr : {x x' y y' : A} (p : x ＝ x') (q : y ＝ y') → B x y → B x' y'
  binary-tr refl refl = id
```
