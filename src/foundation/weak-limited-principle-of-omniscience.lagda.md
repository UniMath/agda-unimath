# The weak limited principle of omniscience

```agda
module foundation.weak-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.disjunction
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **Weak Limited Principle of Omniscience** asserts that for any sequence `f : ℕ → Fin 2` either `f n ＝ 0` for all `n : ℕ` or not. In particular, it is a restricted form of the law of excluded middle.

## Definition

```agda
WLPO : UU lzero
WLPO =
  (f : ℕ → Fin 2) →
  type-disj-Prop
    ( Π-Prop ℕ (λ n → Id-Prop (Fin-Set 2) (f n) (zero-Fin 1)))
    ( neg-Prop (Π-Prop ℕ (λ n → Id-Prop (Fin-Set 2) (f n) (zero-Fin 1))))
```
