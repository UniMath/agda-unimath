# Dirichlet convolution

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.dirichlet-convolution where

open import elementary-number-theory.arithmetic-functions using
  ( type-arithmetic-functions-Ring)
open import elementary-number-theory.bounded-sums-arithmetic-functions using
  ( bounded-sum-arithmetic-function-Ring)
open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( div-ℕ-decidable-Prop)
open import elementary-number-theory.multiplication-natural-numbers using
  ( is-nonzero-left-factor-mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-nonzero-ℕ; is-nonzero-one-ℕ; is-nonzero-succ-ℕ)
open import elementary-number-theory.nonzero-natural-numbers using
  ( nonzero-ℕ; succ-nonzero-ℕ; one-nonzero-ℕ; quotient-div-nonzero-ℕ;
    succ-nonzero-ℕ')

open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop; is-decidable-type-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (refl; inv; _∙_)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import ring-theory.rings using
  ( Ring; type-Ring; zero-Ring; add-Ring; mul-Ring)
```

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  dirichlet-convolution-arithmetic-functions-Ring :
    (f g : type-arithmetic-functions-Ring R) →
    type-arithmetic-functions-Ring R
  dirichlet-convolution-arithmetic-functions-Ring f g (pair zero-ℕ H) =
    ex-falso (H refl) 
  dirichlet-convolution-arithmetic-functions-Ring f g (pair (succ-ℕ n) H) =
    bounded-sum-arithmetic-function-Ring R
      ( succ-ℕ n)
      ( λ x → div-ℕ-decidable-Prop (pr1 x) (succ-ℕ n) (pr2 x))
      ( λ { (pair x K) H →
            mul-Ring R
              ( f ( pair x K))
              ( g ( quotient-div-nonzero-ℕ x (succ-nonzero-ℕ' n) H))})
```
