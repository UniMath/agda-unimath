# The booleans

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.booleans
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import foundation-core.booleans public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equality funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.discrete-types funext univalence truncations
open import foundation.involutions funext univalence
open import foundation.negated-equality funext univalence truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.sets

open import univalent-combinatorics.finite-types funext univalence truncations
open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

The type of **booleans** is a
[2-element type](univalent-combinatorics.2-element-types.md) with elements
`true false : bool`, which is used for reasoning with
[decidable propositions](foundation-core.decidable-propositions.md).

## Properties

### The booleans have decidable equality

```agda
has-decidable-equality-bool : has-decidable-equality bool
has-decidable-equality-bool true true = inl refl
has-decidable-equality-bool true false = inr neq-true-false-bool
has-decidable-equality-bool false true = inr neq-false-true-bool
has-decidable-equality-bool false false = inl refl

bool-Discrete-Type : Discrete-Type lzero
bool-Discrete-Type = bool , has-decidable-equality-bool
```

### The type of booleans is equivalent to `Fin 2`

```agda
bool-Fin-2 : Fin 2 → bool
bool-Fin-2 (inl (inr star)) = true
bool-Fin-2 (inr star) = false

Fin-2-bool : bool → Fin 2
Fin-2-bool true = inl (inr star)
Fin-2-bool false = inr star

abstract
  is-retraction-Fin-2-bool : Fin-2-bool ∘ bool-Fin-2 ~ id
  is-retraction-Fin-2-bool (inl (inr star)) = refl
  is-retraction-Fin-2-bool (inr star) = refl

abstract
  is-section-Fin-2-bool : bool-Fin-2 ∘ Fin-2-bool ~ id
  is-section-Fin-2-bool true = refl
  is-section-Fin-2-bool false = refl

equiv-bool-Fin-2 : Fin 2 ≃ bool
pr1 equiv-bool-Fin-2 = bool-Fin-2
pr2 equiv-bool-Fin-2 =
  is-equiv-is-invertible
    ( Fin-2-bool)
    ( is-section-Fin-2-bool)
    ( is-retraction-Fin-2-bool)
```

### The type of booleans is finite

```agda
is-finite-bool : is-finite bool
is-finite-bool = is-finite-equiv equiv-bool-Fin-2 (is-finite-Fin 2)

number-of-elements-bool : number-of-elements-is-finite is-finite-bool ＝ 2
number-of-elements-bool =
  inv
    ( compute-number-of-elements-is-finite
      ( 2 , equiv-bool-Fin-2)
      ( is-finite-bool))

bool-Finite-Type : Finite-Type lzero
pr1 bool-Finite-Type = bool
pr2 bool-Finite-Type = is-finite-bool
```

### Boolean negation is an involution

```agda
is-involution-neg-bool : is-involution neg-bool
is-involution-neg-bool true = refl
is-involution-neg-bool false = refl
```

### Boolean negation is an equivalence

```agda
abstract
  is-equiv-neg-bool : is-equiv neg-bool
  is-equiv-neg-bool = is-equiv-is-involution is-involution-neg-bool

equiv-neg-bool : bool ≃ bool
pr1 equiv-neg-bool = neg-bool
pr2 equiv-neg-bool = is-equiv-neg-bool
```
