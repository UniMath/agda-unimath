# The weak limited principle of omniscience

```agda
module foundation.weak-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.disjunction-propositions
open import foundation.negation
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.sets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Statement

The {{#concept "Weak Limited Principle of Omniscience"}} asserts that for any
[sequence](foundation.sequences.md) `f : ℕ → Fin 2` either `f n ＝ 0` for all
`n : ℕ` or not. In particular, it is a restricted form of the
[law of excluded middle](foundation.law-of-excluded-middle.md).

```agda
WLPO-Prop : Prop lzero
WLPO-Prop =
  Π₍₋₁₎
    ( ℕ → Fin 2)
    ( λ f →
      disjunction-Prop
        ( Π₍₋₁₎ ℕ (λ n → Id₍₋₁₎ (Fin-Set 2) (f n) (zero-Fin 1)))
        ( ¬₍₋₁₎ (Π₍₋₁₎ ℕ (λ n → Id₍₋₁₎ (Fin-Set 2) (f n) (zero-Fin 1)))))

WLPO : UU lzero
WLPO = type-Prop WLPO-Prop
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
