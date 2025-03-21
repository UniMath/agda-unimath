# The lesser limited principle of omniscience

```agda
module foundation.lesser-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.disjunction
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.booleans
open import foundation-core.fibers-of-maps
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Statement

The {{#concept "lesser limited principle of omniscience" Agda=LLPO}} (LLPO)
asserts that for any [sequence](foundation.sequences.md) of
[booleans](foundation-core.booleans.md) `f : ℕ → bool` such that `f n` is true
for [at most one](foundation-core.propositions.md) `n`, then either `f n` is
false for all even `n` or `f n` is false for all odd `n`.

```agda
prop-LLPO : Prop lzero
prop-LLPO =
  ∀'
    ( ℕ → bool)
    ( λ f →
      function-Prop
        ( is-prop (Σ ℕ (λ n → is-true (f n))))
        ( disjunction-Prop
          ( ∀' ℕ (λ n → function-Prop (is-even-ℕ n) (is-false-Prop (f n))))
          ( ∀' ℕ (λ n → function-Prop (is-odd-ℕ n) (is-false-Prop (f n))))))

LLPO : UU lzero
LLPO = type-Prop prop-LLPO

is-prop-LLPO : is-prop LLPO
is-prop-LLPO = is-prop-type-Prop prop-LLPO
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [Taboos.LLPO](https://martinescardo.github.io/TypeTopology/Taboos.LLPO.html)
  at TypeTopology
- [lesser limited principle of omniscience](https://ncatlab.org/nlab/show/lesser+limited+principle+of+omniscience)
  at $n$Lab
