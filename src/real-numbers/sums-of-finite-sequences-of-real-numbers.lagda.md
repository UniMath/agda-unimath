# Sums of finite sequences of real numbers

```agda
module real-numbers.sums-of-finite-sequences-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import lists.finite-sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.large-additive-group-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.rational-real-numbers
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
