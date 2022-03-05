# Negation

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.negation where

open import foundation-core.empty-types using (empty)
open import foundation-core.universe-levels using (Level; UU)
```

## Idea

The Curry-Howard interpretation of negation in type theory is the interpretation of the proposition `P ⇒ ⊥` using propositions as types. Thus, the negation of a type `A` is the type `A → empty`.

## Definition

```agda
¬ : {l : Level} → UU l → UU l
¬ A = A → empty

map-neg : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬ Q → ¬ P)
map-neg f nq p = nq (f p)
```
