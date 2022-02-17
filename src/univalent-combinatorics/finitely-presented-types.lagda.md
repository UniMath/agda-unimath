# Finitely presented types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.finitely-presented-types where

open import elementary-number-theory.equality-standard-finite-types using
  ( Fin-Set)
open import elementary-number-theory.natural-numbers using (ℕ)
open import elementary-number-theory.standard-finite-types using (Fin)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; map-equiv; is-equiv-htpy-equiv)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (_∘_)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using (UU-Prop; type-Prop)
open import foundation.set-presented-types using (has-set-presentation-Prop)
open import foundation.set-truncations using
  ( type-trunc-Set; unit-trunc-Set; is-surjective-unit-trunc-Set)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.finite-choice using (finite-choice-Fin)
open import univalent-combinatorics.finite-connected-components using
  ( has-cardinality-components; has-cardinality-components-Prop)
```

## Idea

A type is said to be finitely presented if it is presented by a standard finite type.

```agda
has-finite-presentation-Prop :
  {l1 : Level} (k : ℕ) (A : UU l1) → UU-Prop l1
has-finite-presentation-Prop k A =
  has-set-presentation-Prop (Fin-Set k) A

has-finite-presentation :
  {l1 : Level} (k : ℕ) (A : UU l1) → UU l1
has-finite-presentation k A = type-Prop (has-finite-presentation-Prop k A)
  
has-finite-presentation-has-cardinality-components :
  {l : Level} {k : ℕ} {A : UU l} → has-cardinality-components k A →
  has-finite-presentation k A
has-finite-presentation-has-cardinality-components {l} {k} {A} H =
  apply-universal-property-trunc-Prop H
    ( has-finite-presentation-Prop k A)
    ( λ e →
      apply-universal-property-trunc-Prop
        ( P2 e)
        ( has-finite-presentation-Prop k A)
        ( λ g →
          unit-trunc-Prop
            ( pair
              ( λ x → pr1 (g x))
              ( is-equiv-htpy-equiv e (λ x → pr2 (g x))))))
  where
  P1 : (e : Fin k ≃ type-trunc-Set A) (x : Fin k) →
       type-trunc-Prop (fib unit-trunc-Set (map-equiv e x))
  P1 e x = is-surjective-unit-trunc-Set A (map-equiv e x)
  P2 : (e : Fin k ≃ type-trunc-Set A) →
       type-trunc-Prop ((x : Fin k) → fib unit-trunc-Set (map-equiv e x))
  P2 e = finite-choice-Fin (P1 e)

has-cardinality-components-has-finite-presentation :
  {l : Level} {k : ℕ} {A : UU l} → has-finite-presentation k A →
  has-cardinality-components k A
has-cardinality-components-has-finite-presentation {l} {k} {A} H =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-components-Prop k A)
    ( λ { (pair f E) → unit-trunc-Prop (pair (unit-trunc-Set ∘ f) E)})
```
