---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.negation where

open import foundation.empty-type using (empty)
open import foundation.universe-levels using (UU; Level)
```

# Negation

Here we introduce the negation operation, following the Curry-Howard interpretation of logic into type theory. Properties of double negation are proven in `double-negation`.

```agda
¬ : {l : Level} → UU l → UU l
¬ A = A → empty

functor-neg : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬ Q → ¬ P)
functor-neg f nq p = nq (f p)
```
