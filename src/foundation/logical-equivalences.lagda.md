# Logical equivalences

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.logical-equivalences where

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.dependent-pair-types using (pair; pr1; pr2)
open import foundation-core.equivalences using
  ( _≃_; map-equiv; map-inv-equiv; is-equiv)
open import foundation-core.functions using (_∘_)
open import foundation-core.universe-levels using (UU; Level; _⊔_)

open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-prod; is-prop-function-type;
    is-equiv-is-prop; type-hom-Prop; is-prop-type-equiv-Prop)
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

## Properties

### The type of logical equivalences between propositions is a proposition

```agda
abstract
  is-prop-iff :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → is-prop (P ⇔ Q)
  is-prop-iff P Q =
    is-prop-prod
      ( is-prop-function-type (pr2 Q))
      ( is-prop-function-type (pr2 P))
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
equiv-iff' :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (P ⇔ Q) → (pr1 P ≃ pr1 Q)
pr1 (equiv-iff' P Q t) = pr1 t
pr2 (equiv-iff' P Q t) = is-equiv-is-prop (pr2 P) (pr2 Q) (pr2 t)

equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (type-hom-Prop P Q) → (type-hom-Prop Q P) → pr1 P ≃ pr1 Q
equiv-iff P Q f g = equiv-iff' P Q (pair f g)

iff-equiv :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (pr1 P ≃ pr1 Q) → (P ⇔ Q)
pr1 (iff-equiv P Q e) = map-equiv e
pr2 (iff-equiv P Q e) = map-inv-equiv e

abstract
  is-equiv-equiv-iff :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
    is-equiv (equiv-iff' P Q)
  is-equiv-equiv-iff P Q =
    is-equiv-is-prop
      ( is-prop-iff P Q)
      ( is-prop-type-equiv-Prop P Q)
      ( iff-equiv P Q)

equiv-equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (P ⇔ Q) ≃ (type-Prop P ≃ type-Prop Q)
pr1 (equiv-equiv-iff P Q) = equiv-iff' P Q
pr2 (equiv-equiv-iff P Q) = is-equiv-equiv-iff P Q
```
