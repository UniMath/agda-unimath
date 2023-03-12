# The limited principle of omniscience (LPO)

```agda
module foundation.limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.disjunction
open import foundation.existential-quantification

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **Limited Principle of Omniscience** asserts that for every sequence `f : ℕ → Fin 2` either there exists an `n` such that `f n ＝ 1` or for all `n` we have `f n ＝ 0`.

## Definition

```agda
LPO : UU lzero
LPO =
  (f : ℕ → Fin 2) →
  type-disj-Prop
    ( ∃-Prop ℕ (λ n → f n ＝ one-Fin 1))
    ( Π-Prop ℕ (λ n → Id-Prop (Fin-Set 2) (f n) (zero-Fin 1)))
```
