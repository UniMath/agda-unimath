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
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.idempotent-maps
open import foundation.propositional-truncations
open import foundation.truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
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

### The [wild quasigroup](structured-types.wild-quasigroups.md) of a Steiner triple system

```agda
mul-Steiner-Triple-System :
  {n : ℕ} (X : Steiner-Triple-System n) →
  pr1 (pr1 X) → pr1 (pr1 X) → pr1 (pr1 X)
mul-Steiner-Triple-System {n} ((X , fin-X) , trip-X , sts-X) x y with has-decidable-equality-has-cardinality-ℕ n fin-X x y
... | inl p = x
... | inr np = {!   !}
  where
  xyz : {!   !}
  xyz = {!   !}

Steiner-Triple-System-Wild-Quasigroup :
  {n : ℕ} → Steiner-Triple-System n → Wild-Quasigroup lzero
pr1 (pr1 (Steiner-Triple-System-Wild-Quasigroup ((X , _) , _))) = X
pr2 (pr1 (Steiner-Triple-System-Wild-Quasigroup X)) =
  mul-Steiner-Triple-System X
pr1 (pr2 (Steiner-Triple-System-Wild-Quasigroup X)) y = {!   !}
pr2 (pr2 (Steiner-Triple-System-Wild-Quasigroup X)) x = {!   !}
```

### The wild quasigroup of a Steiner triple system is [idempotent](foundation.idempotent-maps.md)

That is, `mul-Steiner-Triple-System X x x ＝ x` for any Steiner triple system
`X` and `x : X`.

```agda
is-idempotent-mul-Steiner-Triple-System :
  {n : ℕ} {X : Steiner-Triple-System n} (x : pr1 (pr1 X)) →
  mul-Steiner-Triple-System X x x ＝ x
is-idempotent-mul-Steiner-Triple-System x = {! refl  !}
```
