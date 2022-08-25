---
title: Finitely presented types
---

```agda
module univalent-combinatorics.finitely-presented-types where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; map-equiv; is-equiv-htpy-equiv; _∘e_; inv-equiv)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (_∘_)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; all-elements-equal; is-prop-all-elements-equal)
open import foundation.set-presented-types using (has-set-presentation-Prop)
open import foundation.set-truncations using
  ( type-trunc-Set; unit-trunc-Set; is-surjective-unit-trunc-Set)
open import foundation.sets using (Id-Prop)
open import foundation.subtypes using (eq-type-subtype)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.finite-choice using (finite-choice-Fin)
open import univalent-combinatorics.finite-connected-components using
  ( has-cardinality-components; has-cardinality-components-Prop)
open import univalent-combinatorics.finite-types using (eq-cardinality)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; is-injective-Fin; Fin-Set)
```

## Idea

A type is said to be finitely presented if it is presented by a standard finite type.

## Definition

### To have a presentation of cardinality `k`

```agda
has-presentation-of-cardinality-Prop :
  {l1 : Level} (k : ℕ) (A : UU l1) → UU-Prop l1
has-presentation-of-cardinality-Prop k A =
  has-set-presentation-Prop (Fin-Set k) A

has-presentation-of-cardinality : {l1 : Level} (k : ℕ) (A : UU l1) → UU l1
has-presentation-of-cardinality k A = type-Prop (has-presentation-of-cardinality-Prop k A)
```

### Finitely presented types

```agda
is-finitely-presented : {l1 : Level} → UU l1 → UU l1
is-finitely-presented A =
  Σ ℕ (λ k → has-presentation-of-cardinality k A)
```

## Properties

### A type has finitely many connected components if and only if it has a finite presentation

```agda
has-presentation-of-cardinality-has-cardinality-components :
  {l : Level} (k : ℕ) {A : UU l} → has-cardinality-components k A →
  has-presentation-of-cardinality k A
has-presentation-of-cardinality-has-cardinality-components {l} k {A} H =
  apply-universal-property-trunc-Prop H
    ( has-presentation-of-cardinality-Prop k A)
    ( λ e →
      apply-universal-property-trunc-Prop
        ( P2 e)
        ( has-presentation-of-cardinality-Prop k A)
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
  P2 e = finite-choice-Fin k (P1 e)

has-cardinality-components-has-presentation-of-cardinality :
  {l : Level} (k : ℕ) {A : UU l} → has-presentation-of-cardinality k A →
  has-cardinality-components k A
has-cardinality-components-has-presentation-of-cardinality {l} k {A} H =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-components-Prop k A)
    ( λ { (pair f E) → unit-trunc-Prop (pair (unit-trunc-Set ∘ f) E)})
```

### To be finitely presented is a property

```agda
all-elements-equal-is-finitely-presented :
  {l1 : Level} {A : UU l1} → all-elements-equal (is-finitely-presented A)
all-elements-equal-is-finitely-presented {l1} {A} (pair k K) (pair l L) =
  eq-type-subtype
    ( λ n → has-set-presentation-Prop (Fin-Set n) A)
    ( eq-cardinality
      ( has-cardinality-components-has-presentation-of-cardinality k K)
      ( has-cardinality-components-has-presentation-of-cardinality l L))

is-prop-is-finitely-presented :
  {l1 : Level} {A : UU l1} → is-prop (is-finitely-presented A)
is-prop-is-finitely-presented =
  is-prop-all-elements-equal all-elements-equal-is-finitely-presented

is-finitely-presented-Prop : {l : Level} (A : UU l) → UU-Prop l
pr1 (is-finitely-presented-Prop A) = is-finitely-presented A
pr2 (is-finitely-presented-Prop A) = is-prop-is-finitely-presented
```
