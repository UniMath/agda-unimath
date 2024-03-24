# The limited principle of omniscience

```agda
module foundation.limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Statement

The
{{#concept "limited principle of omniscience" WDID=Q6549544 WD="limited principle of omniscience" Agda=LPO}}
(LPO) asserts that for every [sequence](foundation.sequences.md) `f : ℕ → Fin 2`
there either [exists](foundation.existential-quantification.md) an `n` such that
`f n ＝ 1` or for all `n` we have `f n ＝ 0`.

```agda
LPO : UU lzero
LPO =
  (f : ℕ → Fin 2) →
  type-disjunction-Prop
    ( ∃ ℕ (λ n → Id-Prop (Fin-Set 2) (f n) (one-Fin 1)))
    ( ∀' ℕ (λ n → Id-Prop (Fin-Set 2) (f n) (zero-Fin 1)))
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
