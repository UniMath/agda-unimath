# Sums of natural numbers

```agda
module elementary-number-theory.sums-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
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
open import foundation.whiskering-homotopies-composition

open import lists.lists

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The values of a map `f : X → ℕ` out of a finite type `X` can be summed up.

## Definition

### Sums of lists of natural numbers

```agda
sum-list-ℕ : list ℕ → ℕ
sum-list-ℕ = fold-list 0 add-ℕ
```

### Sums of natural numbers indexed by a standard finite type

```agda
sum-Fin-ℕ : (k : ℕ) → (Fin k → ℕ) → ℕ
sum-Fin-ℕ zero-ℕ f = zero-ℕ
sum-Fin-ℕ (succ-ℕ k) f = (sum-Fin-ℕ k (λ x → f (inl x))) +ℕ (f (inr star))
```

### Sums of natural numbers indexed by a type equipped with a counting

```agda
sum-count-ℕ : {l : Level} {A : UU l} (e : count A) → (f : A → ℕ) → ℕ
sum-count-ℕ (pair k e) f = sum-Fin-ℕ k (f ∘ (map-equiv e))
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
  htpy-sum-Fin-ℕ :
    (k : ℕ) {f g : Fin k → ℕ} (H : f ~ g) → sum-Fin-ℕ k f ＝ sum-Fin-ℕ k g
  htpy-sum-Fin-ℕ zero-ℕ H = refl
  htpy-sum-Fin-ℕ (succ-ℕ k) H =
    ap-add-ℕ
      ( htpy-sum-Fin-ℕ k (λ x → H (inl x)))
      ( H (inr star))

abstract
  htpy-sum-count-ℕ :
    {l : Level} {A : UU l} (e : count A) {f g : A → ℕ} (H : f ~ g) →
    sum-count-ℕ e f ＝ sum-count-ℕ e g
  htpy-sum-count-ℕ (pair k e) H = htpy-sum-Fin-ℕ k (H ·r (map-equiv e))
```

### Summing up the same value `m` times is multiplication by `m`

```agda
abstract
  constant-sum-Fin-ℕ :
    (m n : ℕ) → sum-Fin-ℕ m (const n) ＝ m *ℕ n
  constant-sum-Fin-ℕ zero-ℕ n = refl
  constant-sum-Fin-ℕ (succ-ℕ m) n = ap (_+ℕ n) (constant-sum-Fin-ℕ m n)

abstract
  constant-sum-count-ℕ :
    {l : Level} {A : UU l} (e : count A) (n : ℕ) →
    sum-count-ℕ e (const n) ＝ (number-of-elements-count e) *ℕ n
  constant-sum-count-ℕ (pair m e) n = constant-sum-Fin-ℕ m n
```

### Each of the summands is less than or equal to the total sum

```text
leq-sum-Fin-ℕ :
  {k : ℕ} (f : Fin k → ℕ) (x : Fin k) → leq-ℕ (f x) (sum-Fin-ℕ f)
leq-sum-Fin-ℕ {succ-ℕ k} f x = {!leq-add-ℕ!}
```
