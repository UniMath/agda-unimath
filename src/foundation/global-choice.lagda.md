# Global choice

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.global-choice where

open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso; empty-Prop)
open import foundation.equivalences using (_≃_; map-equiv; map-inv-equiv)
open import foundation.functions using (_∘_)
open import foundation.functoriality-propositional-truncation using
  ( functor-trunc-Prop)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; apply-universal-property-trunc-Prop)
open import foundation.universe-levels using (Level; UU; lsuc)

open import univalent-combinatorics.2-element-types using
  ( no-section-type-UU-Fin-Level-two-ℕ)
open import univalent-combinatorics.standard-finite-types using
  ( zero-Fin)
```

## Idea

Global choice is the principle that there is a map from `type-trunc-Prop A` back into `A`, for any type `A`. Here, we say that a type `A` satisfies global choice if there is such a map.

## Definition

```agda
global-choice : {l : Level} → UU l → UU l
global-choice X = type-trunc-Prop X → X

Global-Choice : (l : Level) → UU (lsuc l)
Global-Choice l = (A : UU l) → global-choice A

global-choice-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  global-choice X → global-choice Y
global-choice-equiv e f =
  (map-equiv e ∘ f) ∘ (functor-trunc-Prop (map-inv-equiv e))

global-choice-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  global-choice Y → global-choice X
global-choice-equiv' e f =
  (map-inv-equiv e ∘ f) ∘ (functor-trunc-Prop (map-equiv e))
```

```agda
elim-trunc-Prop-is-decidable :
  {l : Level} {A : UU l} → is-decidable A → type-trunc-Prop A → A
elim-trunc-Prop-is-decidable (inl a) x = a
elim-trunc-Prop-is-decidable (inr f) x =
  ex-falso (apply-universal-property-trunc-Prop x empty-Prop f)
```

```agda
abstract
  no-global-section :
    {l : Level} → ¬ ((X : UU l) → type-trunc-Prop X → X)
  no-global-section f =
    no-section-type-UU-Fin-Level-two-ℕ
      ( λ X →
        f (pr1 X) (functor-trunc-Prop (λ e → map-equiv e zero-Fin) (pr2 X)))
```
