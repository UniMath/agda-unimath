---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.binary-relations where

open import foundations.levels using (UU; Level; _⊔_)
```

# Properties of binary relations

```agda
is-reflexive : {l1 l2 : Level} {A : UU l1} → (A → A → UU l2) → UU (l1 ⊔ l2)
is-reflexive {A = A} R = (x : A) → R x x

is-symmetric : {l1 l2 : Level} {A : UU l1} → (A → A → UU l2) → UU (l1 ⊔ l2)
is-symmetric {A = A} R = (x y : A) → R x y → R y x

is-transitive : {l1 l2 : Level} {A : UU l1} → (A → A → UU l2) → UU (l1 ⊔ l2)
is-transitive {A = A} R = (x y z : A) → R x y → R y z → R x z
```
