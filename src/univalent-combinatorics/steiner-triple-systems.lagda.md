# Steiner triple systems

```agda
{-# OPTIONS --lossy-unification #-}

module univalent-combinatorics.steiner-triple-systems where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-equivalences
open import foundation.decidable-equality
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.double-negation-stable-propositions
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.idempotent-maps
open import foundation.inhabited-types
open import foundation.negated-equality
open import foundation.propositional-truncations
open import foundation.truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
open import foundation-core.propositions
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.truncation-levels

open import structured-types.wild-quasigroups

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.steiner-systems
```

</details>

## Definition

```agda
Steiner-Triple-System : ℕ → UU (lsuc lzero)
Steiner-Triple-System n = Steiner-System 2 3 n
```

## Properties

### Two pairwise distinct elements `x, y ∈ X` uniquely determine a third

```agda
module _
  {n : ℕ}
  (X : Steiner-Triple-System n)
  (x y : type-Steiner-System X)
  (np : x ≠ y)
  where

  all-elements-equal-lem-mul-Steiner-Triple-System :
    all-elements-equal
      (Σ
        (type-Steiner-System X)
        (λ z →
          type-Decidable-Prop
            (subtype-subtype-map-Steiner-System X
              (decidable-subtype-standard-2-Element-Decidable-Subtype
                (has-decidable-equality-Steiner-System X) np)
              (has-two-elements-type-standard-2-Element-Decidable-Subtype
                (has-decidable-equality-Steiner-System X) np)
              ( z))))
  all-elements-equal-lem-mul-Steiner-Triple-System (z , _) (w , _) =
    eq-type-subtype
      ( λ a → prop-Decidable-Prop _)
      ( {!   !})

  lem-mul-Steiner-Triple-System :
    is-contr (Σ (type-Steiner-System X) (λ z → type-Decidable-Prop
      (subtype-subtype-map-Steiner-System X
        (decidable-subtype-standard-2-Element-Decidable-Subtype
          (has-decidable-equality-Steiner-System X) np)
        (has-two-elements-type-standard-2-Element-Decidable-Subtype
          (has-decidable-equality-Steiner-System X) np)
        z)))
  lem-mul-Steiner-Triple-System =
    is-contr-is-inhabited-is-prop
    ( is-prop-all-elements-equal {!   !})
    ( unit-trunc
      ( x , pr2
        (pr1
          (pr2 (pr2 X)
            (decidable-subtype-standard-2-Element-Decidable-Subtype
              (has-decidable-equality-Steiner-System X) np)
            (has-two-elements-type-standard-2-Element-Decidable-Subtype
              (has-decidable-equality-Steiner-System X) np)))
        x (inl refl)))
```

### The [wild quasigroup](structured-types.wild-quasigroups.md) of a Steiner triple system

```agda
mul-Steiner-Triple-System :
  {n : ℕ} (X : Steiner-Triple-System n) →
  type-Steiner-System X → type-Steiner-System X → type-Steiner-System X
mul-Steiner-Triple-System {n} X x y with has-decidable-equality-Steiner-System X x y
... | inl p = x
... | inr np = pr1 (center (lem-mul-Steiner-Triple-System X x y np))

is-left-equiv-mul-Steiner-System :
  {n : ℕ} (X : Steiner-Triple-System n) (x : type-Steiner-System X) →
  is-equiv (λ y → mul-Steiner-Triple-System X y x)
is-left-equiv-mul-Steiner-System X x = {!   !}

is-right-equiv-mul-Steiner-System :
  {n : ℕ} (X : Steiner-Triple-System n) (x : type-Steiner-System X) →
  is-equiv (mul-Steiner-Triple-System X x)
is-right-equiv-mul-Steiner-System X x = {!   !}

Steiner-Triple-System-Wild-Quasigroup :
  {n : ℕ} → Steiner-Triple-System n → Wild-Quasigroup lzero
pr1 (pr1 (Steiner-Triple-System-Wild-Quasigroup ((X , _) , _))) = X
pr2 (pr1 (Steiner-Triple-System-Wild-Quasigroup X)) =
  mul-Steiner-Triple-System X
pr1 (pr2 (Steiner-Triple-System-Wild-Quasigroup X)) =
  is-left-equiv-mul-Steiner-System X
pr2 (pr2 (Steiner-Triple-System-Wild-Quasigroup X)) =
  is-right-equiv-mul-Steiner-System X
```

### The wild quasigroup of a Steiner triple system is [idempotent](foundation.idempotent-maps.md)

That is, `mul-Steiner-Triple-System X x x ＝ x` for any Steiner triple system
`X` and `x : X`.

```agda
is-idempotent-mul-Steiner-Triple-System :
  {n : ℕ} {X : Steiner-Triple-System n} (x : type-Steiner-System X) →
  mul-Steiner-Triple-System X x x ＝ x
is-idempotent-mul-Steiner-Triple-System x = {! refl  !}
```

### The wild quasigroup of a Steiner triple system is commutative

```agda
is-commutative-mul-Steiner-Triple-System :
  {n : ℕ} {X : Steiner-Triple-System n} (x y : type-Steiner-System X) →
  mul-Steiner-Triple-System X x y ＝ mul-Steiner-Triple-System X y x
is-commutative-mul-Steiner-Triple-System x y = {!   !}
```
