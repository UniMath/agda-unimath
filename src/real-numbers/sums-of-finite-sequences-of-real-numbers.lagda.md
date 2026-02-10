# Sums of finite sequences of real numbers

```agda
module real-numbers.sums-of-finite-sequences-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import lists.finite-sequences

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.large-additive-group-of-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence of real numbers" Agda=sum-fin-sequence-ℝ}}
extends the [addition](real-numbers.addition-real-numbers.md) operation on
[real numbers](real-numbers.dedekind-real-numbers.md) to any
[finite sequence](lists.finite-sequences.md) of real numbers.

## Definition

```agda
sum-fin-sequence-ℝ : {l : Level} (n : ℕ) → fin-sequence (ℝ l) n → ℝ l
sum-fin-sequence-ℝ {l} = sum-fin-sequence-type-Ab (ab-add-ℝ l)
```

## Properties

### Permutations preserve sums

```agda
abstract
  preserves-sum-permutation-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (σ : Permutation n) (a : fin-sequence (ℝ l) n) →
    sum-fin-sequence-ℝ n a ＝ sum-fin-sequence-ℝ n (a ∘ map-equiv σ)
  preserves-sum-permutation-fin-sequence-ℝ {l} =
    preserves-sum-permutation-fin-sequence-type-Ab (ab-add-ℝ l)
```

### Constant sums are multiples

```agda
abstract
  sum-constant-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (c : ℝ l) →
    sum-fin-sequence-ℝ n (λ _ → c) ＝ real-ℕ n *ℝ c
  sum-constant-fin-sequence-ℝ {l} n c =
    ( sum-constant-fin-sequence-type-Ab (ab-add-ℝ l) n c) ∙
    ( inv (left-mul-real-ℕ n c))
```

### If `aᵢ ≤ bᵢ` for all i, then the sum of the `aᵢ` is less than or equal to the sum of the `bᵢ`

```agda
abstract
  preserves-leq-sum-fin-sequence-ℝ :
    {l1 l2 : Level}
    (n : ℕ) (a : fin-sequence (ℝ l1) n) (b : fin-sequence (ℝ l2) n) →
    ((i : Fin n) → leq-ℝ (a i) (b i)) →
    leq-ℝ (sum-fin-sequence-ℝ n a) (sum-fin-sequence-ℝ n b)
  preserves-leq-sum-fin-sequence-ℝ {l1} {l2} 0 _ _ _ =
    leq-sim-ℝ (sim-raise-raise-ℝ l1 l2 zero-ℝ)
  preserves-leq-sum-fin-sequence-ℝ (succ-ℕ n) a b aᵢ≤bᵢ =
    preserves-leq-add-ℝ
      ( preserves-leq-sum-fin-sequence-ℝ
        ( n)
        ( a ∘ inl-Fin n)
        ( b ∘ inl-Fin n)
        ( aᵢ≤bᵢ ∘ inl-Fin n))
      ( aᵢ≤bᵢ (neg-one-Fin n))
```

### Homotopic finite sequences have the same sums

```agda
abstract
  htpy-sum-fin-sequence-ℝ :
    {l : Level} (n : ℕ) {a b : fin-sequence (ℝ l) n} → a ~ b →
    sum-fin-sequence-ℝ n a ＝ sum-fin-sequence-ℝ n b
  htpy-sum-fin-sequence-ℝ {l} = htpy-sum-fin-sequence-type-Ab (ab-add-ℝ l)
```

### `∑ aₙ + ∑ bₙ = ∑ (aₙ + bₙ)`

```agda
abstract
  interchange-add-sum-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (a b : fin-sequence (ℝ l) n) →
    sum-fin-sequence-ℝ n a +ℝ sum-fin-sequence-ℝ n b ＝
    sum-fin-sequence-ℝ n (λ i → a i +ℝ b i)
  interchange-add-sum-fin-sequence-ℝ {l} =
    interchange-add-sum-fin-sequence-type-Commutative-Ring
      ( commutative-ring-ℝ l)
```

### Multiplication distributes over sums

```agda
abstract
  left-distributive-mul-sum-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (x : ℝ l) (f : fin-sequence (ℝ l) n) →
    x *ℝ sum-fin-sequence-ℝ n f ＝ sum-fin-sequence-ℝ n (λ i → x *ℝ f i)
  left-distributive-mul-sum-fin-sequence-ℝ {l} =
    left-distributive-mul-sum-fin-sequence-type-Commutative-Ring
      ( commutative-ring-ℝ l)

  right-distributive-mul-sum-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (f : fin-sequence (ℝ l) n) (x : ℝ l) →
    sum-fin-sequence-ℝ n f *ℝ x ＝ sum-fin-sequence-ℝ n (λ i → f i *ℝ x)
  right-distributive-mul-sum-fin-sequence-ℝ {l} =
    right-distributive-mul-sum-fin-sequence-type-Commutative-Ring
      ( commutative-ring-ℝ l)
```

### Sums of zeroes are zero

```agda
abstract
  sum-zero-fin-sequence-ℝ :
    {l : Level} (n : ℕ) →
    sum-fin-sequence-ℝ n (λ _ → raise-zero-ℝ l) ＝ raise-zero-ℝ l
  sum-zero-fin-sequence-ℝ {l} =
    sum-zero-fin-sequence-type-Commutative-Ring
      ( commutative-ring-ℝ l)
```

### If `aₙ ≤ bₙ` for all `n`, then `∑ aₙ ≤ ∑ bₙ`

```agda
abstract
  leq-sum-fin-sequence-ℝ :
    {l1 l2 : Level} (n : ℕ) →
    (a : fin-sequence (ℝ l1) n) (b : fin-sequence (ℝ l2) n) →
    ((k : Fin n) → leq-ℝ (a k) (b k)) →
    leq-ℝ (sum-fin-sequence-ℝ n a) (sum-fin-sequence-ℝ n b)
  leq-sum-fin-sequence-ℝ {l1} {l2} 0 _ _ _ =
    leq-sim-ℝ
      ( transitive-sim-ℝ _ _ _ (sim-raise-ℝ l2 zero-ℝ) (sim-raise-ℝ' l1 zero-ℝ))
  leq-sum-fin-sequence-ℝ (succ-ℕ n) a b H =
    preserves-leq-add-ℝ
      ( leq-sum-fin-sequence-ℝ
        ( n)
        ( a ∘ inl-Fin n)
        ( b ∘ inl-Fin n)
        ( H ∘ inl-Fin n))
      ( H (neg-one-Fin n))
```
