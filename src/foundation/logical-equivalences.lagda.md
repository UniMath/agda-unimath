# Logical equivalences

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.logical-equivalences where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.functions using (_∘_)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

Logical equivalences between two types `A` and `B` consist of a map `A → B` and a map `B → A`. The type of logical equivalences between types is the Curry-Howard interpretation of logical equivalences between propositions.

## Definition

```agda
_↔_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↔ B = (A → B) × (B → A)
```

## Properties

### Composition of logical equivalences

```agda
_∘iff_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (B ↔ C) → (A ↔ B) → (A ↔ C)
pr1 (pair g1 g2 ∘iff pair f1 f2) = g1 ∘ f1
pr2 (pair g1 g2 ∘iff pair f1 f2) = f2 ∘ g2
```
