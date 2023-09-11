# The booleans

```agda
module foundation.booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.sets

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The type of booleans is a 2-element type with elements `true false : bool`,
which is used for reasoning with decidable propositions.

## Definition

### The booleans

```agda
data bool : UU lzero where
  true false : bool

{-# BUILTIN BOOL bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}
```

### Raising universe levels of the booleans

```agda
raise-bool : (l : Level) → UU l
raise-bool l = raise l bool

raise-true : (l : Level) → raise-bool l
raise-true l = map-raise true

raise-false : (l : Level) → raise-bool l
raise-false l = map-raise false

compute-raise-bool : (l : Level) → bool ≃ raise-bool l
compute-raise-bool l = compute-raise l bool
```

### Equality on the booleans

```agda
Eq-bool : bool → bool → UU lzero
Eq-bool true true = unit
Eq-bool true false = empty
Eq-bool false true = empty
Eq-bool false false = unit

refl-Eq-bool : (x : bool) → Eq-bool x x
refl-Eq-bool true = star
refl-Eq-bool false = star

Eq-eq-bool :
  {x y : bool} → x ＝ y → Eq-bool x y
Eq-eq-bool {x = x} refl = refl-Eq-bool x

eq-Eq-bool :
  {x y : bool} → Eq-bool x y → x ＝ y
eq-Eq-bool {true} {true} star = refl
eq-Eq-bool {false} {false} star = refl

neq-false-true-bool :
  ¬ (false ＝ true)
neq-false-true-bool ()
```

## Structure

### The boolean operators

```agda
neg-bool : bool → bool
neg-bool true = false
neg-bool false = true

conjunction-bool : bool → (bool → bool)
conjunction-bool true true = true
conjunction-bool true false = false
conjunction-bool false true = false
conjunction-bool false false = false

disjunction-bool : bool → (bool → bool)
disjunction-bool true true = true
disjunction-bool true false = true
disjunction-bool false true = true
disjunction-bool false false = false
```

## Properties

### The booleans are a set

```agda
abstract
  is-prop-Eq-bool : (x y : bool) → is-prop (Eq-bool x y)
  is-prop-Eq-bool true true = is-prop-unit
  is-prop-Eq-bool true false = is-prop-empty
  is-prop-Eq-bool false true = is-prop-empty
  is-prop-Eq-bool false false = is-prop-unit

abstract
  is-set-bool : is-set bool
  is-set-bool =
    is-set-prop-in-id
      ( Eq-bool)
      ( is-prop-Eq-bool)
      ( refl-Eq-bool)
      ( λ x y → eq-Eq-bool)

bool-Set : Set lzero
pr1 bool-Set = bool
pr2 bool-Set = is-set-bool
```

### The type of booleans is equivalent to `Fin 2`

```agda
bool-Fin-two-ℕ : Fin 2 → bool
bool-Fin-two-ℕ (inl (inr star)) = true
bool-Fin-two-ℕ (inr star) = false

Fin-two-ℕ-bool : bool → Fin 2
Fin-two-ℕ-bool true = inl (inr star)
Fin-two-ℕ-bool false = inr star

abstract
  is-retraction-Fin-two-ℕ-bool : (Fin-two-ℕ-bool ∘ bool-Fin-two-ℕ) ~ id
  is-retraction-Fin-two-ℕ-bool (inl (inr star)) = refl
  is-retraction-Fin-two-ℕ-bool (inr star) = refl

abstract
  is-section-Fin-two-ℕ-bool : (bool-Fin-two-ℕ ∘ Fin-two-ℕ-bool) ~ id
  is-section-Fin-two-ℕ-bool true = refl
  is-section-Fin-two-ℕ-bool false = refl

equiv-bool-Fin-two-ℕ : Fin 2 ≃ bool
pr1 equiv-bool-Fin-two-ℕ = bool-Fin-two-ℕ
pr2 equiv-bool-Fin-two-ℕ =
  is-equiv-is-invertible
    ( Fin-two-ℕ-bool)
    ( is-section-Fin-two-ℕ-bool)
    ( is-retraction-Fin-two-ℕ-bool)
```

### The type of booleans is finite

```agda
is-finite-bool : is-finite bool
is-finite-bool = is-finite-equiv equiv-bool-Fin-two-ℕ (is-finite-Fin 2)

bool-𝔽 : 𝔽 lzero
pr1 bool-𝔽 = bool
pr2 bool-𝔽 = is-finite-bool
```

### Boolean negation has no fixed points

```agda
neq-neg-bool : (b : bool) → ¬ (b ＝ neg-bool b)
neq-neg-bool true ()
neq-neg-bool false ()
```

### Boolean negation is an involution

```agda
neg-neg-bool : (neg-bool ∘ neg-bool) ~ id
neg-neg-bool true = refl
neg-neg-bool false = refl
```

### Boolean negation is an equivalence

```agda
abstract
  is-equiv-neg-bool : is-equiv neg-bool
  pr1 (pr1 is-equiv-neg-bool) = neg-bool
  pr2 (pr1 is-equiv-neg-bool) = neg-neg-bool
  pr1 (pr2 is-equiv-neg-bool) = neg-bool
  pr2 (pr2 is-equiv-neg-bool) = neg-neg-bool

equiv-neg-bool : bool ≃ bool
pr1 equiv-neg-bool = neg-bool
pr2 equiv-neg-bool = is-equiv-neg-bool
```

### The constant function `const bool bool b` is not an equivalence

```agda
abstract
  not-equiv-const :
    (b : bool) → ¬ (is-equiv (const bool bool b))
  not-equiv-const true (pair (pair g G) (pair h H)) =
    neq-false-true-bool (inv (G false))
  not-equiv-const false (pair (pair g G) (pair h H)) =
    neq-false-true-bool (G true)
```

### The constant function `const bool bool b` is injective

```agda
abstract
  is-injective-const-true : is-injective (const unit bool true)
  is-injective-const-true {star} {star} p = refl

abstract
  is-injective-const-false : is-injective (const unit bool false)
  is-injective-const-false {star} {star} p = refl
```
