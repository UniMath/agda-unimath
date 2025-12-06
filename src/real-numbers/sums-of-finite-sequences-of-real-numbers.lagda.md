# Sums of finite sequences of real numbers

```agda
module real-numbers.sums-of-finite-sequences-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.universe-levels

open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import lists.finite-sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.large-additive-group-of-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in ℝ" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-ℝ}}
extends the operation of [addition](real-numbers.addition-real-numbers.md) on
the [real numbers](real-numbers.dedekind-real-numbers.md) to any
[finite sequence](lists.finite-sequences.md) of real numbers.

## Definition

```agda
sum-fin-sequence-ℝ : {l : Level} (n : ℕ) → fin-sequence (ℝ l) n → ℝ l
sum-fin-sequence-ℝ {l} = sum-fin-sequence-type-Ab (ab-add-ℝ l)
```

## Properties

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
