# Lawvere's fixed point theorem

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.lawveres-fixed-point-theorem where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.existential-quantification using (∃; ∃-Prop; intro-∃)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.identity-types using (Id; inv)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.surjective-maps using (is-surjective)
open import foundation.universe-levels using (Level; UU)
```

## Idea

Lawvere's fixed point theorem asserts that if there is a surjective map `A → (A → B)`, then any map `B → B` must have a fixed point.

## Theorem

```agda
abstract
  fixed-point-theorem-Lawvere :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → A → B} →
    is-surjective f → (h : B → B) → ∃ (λ b → Id (h b) b)
  fixed-point-theorem-Lawvere {A = A} {B} {f} H h =
    apply-universal-property-trunc-Prop
      ( H g)
      ( ∃-Prop (λ b → Id (h b) b))
      ( λ p → intro-∃ (f (pr1 p) (pr1 p)) (inv (htpy-eq (pr2 p) (pr1 p))))
    where
    g : A → B
    g a = h (f a a)
```
