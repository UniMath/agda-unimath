# The weak limited principle of omniscience

```agda
module foundation.weak-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.disjunction
open import foundation.negation
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.sets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Statement

The {{#concept "weak limited principle of omniscience"}} (WLPO) asserts that for
any [sequence](foundation.sequences.md) `f : ℕ → Fin 2` either `f n ＝ 0` for
all `n : ℕ` or not. In particular, it is a restricted form of the
[law of excluded middle](foundation.law-of-excluded-middle.md).

```agda
WLPO-Prop : Prop lzero
WLPO-Prop =
  ∀'
    ( ℕ → Fin 2)
    ( λ f →
      disjunction-Prop
        ( ∀' ℕ (λ n → Id-Prop (Fin-Set 2) (f n) (zero-Fin 1)))
        ( ¬' (∀' ℕ (λ n → Id-Prop (Fin-Set 2) (f n) (zero-Fin 1)))))

WLPO : UU lzero
WLPO = type-Prop WLPO-Prop
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [weak limited principle of omniscience](https://ncatlab.org/nlab/show/weak+limited+principle+of+omniscience)
  at $n$Lab
