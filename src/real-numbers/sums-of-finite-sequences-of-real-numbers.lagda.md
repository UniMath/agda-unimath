# Sums of finite sequences of real numbers

```agda
module real-numbers.sums-of-finite-sequences-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import lists.finite-sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.large-additive-group-of-real-numbers
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
