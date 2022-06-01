# Structure

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.structure where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import
  foundation.type-theoretic-principle-of-choice using
  ( inv-distributive-Π-Σ)
open import foundation.equivalences using (_≃_; _∘e_)
open import foundation.fibers-of-maps using (fib)
open import foundation.functoriality-dependent-pair-types using (equiv-Σ)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Idea

Given a type family `P` on the universe, a `P`-structured type consists of a type `A` equipped with an element of type `P A`.

## Definition

```agda
structure : {l1 l2 : Level} (P : UU l1 → UU l2) → UU (lsuc l1 ⊔ l2)
structure {l1} P = Σ (UU l1) P

fam-structure :
  {l1 l2 l3 : Level} (P : UU l1 → UU l2) (A : UU l3) → UU (lsuc l1 ⊔ l2 ⊔ l3)
fam-structure P A = A → structure P

structure-map :
  {l1 l2 l3 : Level} (P : UU (l1 ⊔ l2) → UU l3) {A : UU l1} {B : UU l2}
  (f : A → B) → UU (l2 ⊔ l3)
structure-map P {A} {B} f = (b : B) → P (fib f b)

hom-structure :
  {l1 l2 l3 : Level} (P : UU (l1 ⊔ l2) → UU l3) →
  UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ l3)
hom-structure P A B = Σ (A → B) (structure-map P)
```
