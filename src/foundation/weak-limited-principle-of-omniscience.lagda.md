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

open import foundation-core.booleans
open import foundation-core.decidable-propositions
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Statement

The {{#concept "weak limited principle of omniscience"}} (WLPO) asserts that for
any [sequence](foundation.sequences.md) `f : ℕ → bool` either `f n` is true for
all `n : ℕ` or it is [not](foundation-core.negation.md). In particular, it is a
restricted form of the
[law of excluded middle](foundation.law-of-excluded-middle.md).

```agda
prop-WLPO : Prop lzero
prop-WLPO =
  ∀' (ℕ → bool) (λ f → is-decidable-Prop (∀' ℕ (λ n → is-true-Prop (f n))))

WLPO : UU lzero
WLPO = type-Prop prop-WLPO

is-prop-WLPO : is-prop WLPO
is-prop-WLPO = is-prop-type-Prop prop-WLPO
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [Taboos.WLPO](https://martinescardo.github.io/TypeTopology/Taboos.WLPO.html)
  at TypeTopology
- [weak limited principle of omniscience](https://ncatlab.org/nlab/show/weak+limited+principle+of+omniscience)
  at $n$Lab
