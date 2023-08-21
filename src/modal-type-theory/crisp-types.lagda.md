# Crisp types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-types where

open import foundation.universe-levels
open import foundation.function-types
open import foundation.identity-types
```

## Idea

TODO: find out where to place the contents of this file

## Properties

```agda
crisp-ind-path :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {@♭ a : A} →
  (C : (@♭ y : A) (p : a ＝ y) → UU l2) →
  C a refl →
  (@♭ y : A) (@♭ p : a ＝ y) → C y p
crisp-ind-path C b _ refl = b
```
