# Sums of natural numbers

```agda
module elementary-number-theory.sums-of-finite-sequences-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.monoid-of-natural-numbers-with-addition
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import lists.finite-sequences
open import foundation.whiskering-homotopies-composition

open import group-theory.sums-of-finite-sequences-of-elements-monoids

open import lists.lists

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The [sums](group-theory.sums-of-finite-sequences-of-elements-monoids.md) of
[finite sequences](lists.finite-sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md) enjoy useful
properties.

## Definition

### Sums of lists of natural numbers

```agda
sum-list-ℕ : list ℕ → ℕ
sum-list-ℕ = fold-list 0 add-ℕ
```

### Sums of natural numbers indexed by a standard finite type

```agda
sum-fin-sequence-ℕ : (k : ℕ) → fin-sequence ℕ k → ℕ
sum-fin-sequence-ℕ = sum-fin-sequence-type-Monoid ℕ-Monoid
```

### Sums of natural numbers indexed by a type equipped with a counting

```agda
sum-count-ℕ : {l : Level} {A : UU l} (e : count A) → (f : A → ℕ) → ℕ
sum-count-ℕ (k , Fin-k≃A) f = sum-fin-sequence-ℕ k (f ∘ map-equiv Fin-k≃A)
```

### Bounded sums of natural numbers

```agda
bounded-sum-ℕ : (u : ℕ) → ((x : ℕ) → le-ℕ x u → ℕ) → ℕ
bounded-sum-ℕ zero-ℕ f = zero-ℕ
bounded-sum-ℕ (succ-ℕ u) f =
  add-ℕ
    ( bounded-sum-ℕ u (λ x H → f x (preserves-le-succ-ℕ x u H)))
    ( f u (succ-le-ℕ u))
```

## Properties

### Sums are invariant under homotopy

```agda
abstract
  htpy-sum-fin-sequence-ℕ :
    (k : ℕ) {f g : Fin k → ℕ} (H : f ~ g) →
    sum-fin-sequence-ℕ k f ＝ sum-fin-sequence-ℕ k g
  htpy-sum-fin-sequence-ℕ = htpy-sum-fin-sequence-type-Monoid ℕ-Monoid

  htpy-sum-count-ℕ :
    {l : Level} {A : UU l} (e : count A) {f g : A → ℕ} (H : f ~ g) →
    sum-count-ℕ e f ＝ sum-count-ℕ e g
  htpy-sum-count-ℕ (pair k e) H = htpy-sum-fin-sequence-ℕ k (H ·r map-equiv e)
```

### Summing up the same value `m` times is multiplication by `m`

```agda
abstract
  constant-sum-fin-sequence-ℕ :
    (m n : ℕ) → sum-fin-sequence-ℕ m (const (Fin m) n) ＝ m *ℕ n
  constant-sum-fin-sequence-ℕ zero-ℕ n = refl
  constant-sum-fin-sequence-ℕ (succ-ℕ m) n =
    ap (_+ℕ n) (constant-sum-fin-sequence-ℕ m n)

  constant-sum-count-ℕ :
    {l : Level} {A : UU l} (e : count A) (n : ℕ) →
    sum-count-ℕ e (const A n) ＝ (number-of-elements-count e) *ℕ n
  constant-sum-count-ℕ (m , e) n = constant-sum-fin-sequence-ℕ m n
```

### Each of the summands is less than or equal to the total sum

```agda
abstract
  leq-sum-fin-sequence-ℕ :
    (k : ℕ) (f : Fin k → ℕ) (x : Fin k) → leq-ℕ (f x) (sum-fin-sequence-ℕ k f)
  leq-sum-fin-sequence-ℕ (succ-ℕ k) f (inl i) =
    transitive-leq-ℕ
      ( f (inl i))
      ( sum-fin-sequence-ℕ k (f ∘ inl))
      ( sum-fin-sequence-ℕ (succ-ℕ k) f)
      ( leq-add-ℕ (sum-fin-sequence-ℕ k (f ∘ inl)) (f (neg-one-Fin k)))
      ( leq-sum-fin-sequence-ℕ k (f ∘ inl) i)
  leq-sum-fin-sequence-ℕ (succ-ℕ k) f (inr star) =
    leq-add-ℕ' (f (neg-one-Fin k)) (sum-fin-sequence-ℕ k (f ∘ inl))
```
