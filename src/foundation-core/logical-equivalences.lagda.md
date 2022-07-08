---
title: Logical equivalences
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.logical-equivalences where

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.dependent-pair-types using (pair; pr1; pr2)
open import foundation-core.equivalences using
  ( _≃_; map-equiv; map-inv-equiv; is-equiv)
open import foundation-core.functions using (_∘_)
open import foundation-core.universe-levels using (UU; Level; _⊔_)

open import foundation-core.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-prod; is-equiv-is-prop)
```

## Idea

Logical equivalences between two types `A` and `B` consist of a map `A → B` and a map `B → A`. The type of logical equivalences between types is the Curry-Howard interpretation of logical equivalences between propositions.

## Definition

### Logical equivalences between types

```agda
_↔_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↔ B = (A → B) × (B → A)
```

### Logical equivalences between propositions

```agda
_⇔_ :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
P ⇔ Q = type-Prop P ↔ type-Prop Q
```

### Composition of logical equivalences

```agda
_∘iff_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (B ↔ C) → (A ↔ B) → (A ↔ C)
pr1 (pair g1 g2 ∘iff pair f1 f2) = g1 ∘ f1
pr2 (pair g1 g2 ∘iff pair f1 f2) = f2 ∘ g2
```

### Logical equivalences between propositions induce equivalences

```agda
module _
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2)
  where
  
  equiv-iff' : (P ⇔ Q) → (type-Prop P ≃ type-Prop Q)
  pr1 (equiv-iff' t) = pr1 t
  pr2 (equiv-iff' t) = is-equiv-is-prop (pr2 P) (pr2 Q) (pr2 t)
  
  equiv-iff :
    (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) →
    type-Prop P ≃ type-Prop Q
  equiv-iff f g = equiv-iff' (pair f g)

  iff-equiv : (type-Prop P ≃ type-Prop Q) → (P ⇔ Q)
  pr1 (iff-equiv e) = map-equiv e
  pr2 (iff-equiv e) = map-inv-equiv e
```
