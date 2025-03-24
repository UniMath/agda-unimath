# The limited principle of omniscience

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.limited-principle-of-omniscience
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.disjunction funext univalence truncations
open import foundation.existential-quantification funext univalence truncations
open import foundation.negation funext
open import foundation.universal-quantification funext univalence truncations
open import foundation.universe-levels

open import foundation-core.booleans
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets

open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Statement

The
{{#concept "limited principle of omniscience" WDID=Q6549544 WD="limited principle of omniscience" Agda=LPO}}
(LPO) asserts that for every [sequence](foundation.sequences.md) `f : ℕ → bool`
there either [exists](foundation.existential-quantification.md) an `n` such that
`f n` is true, [or](foundation.disjunction.md) `f n` is false for all `n`.

```agda
LPO : UU lzero
LPO =
  (f : ℕ → bool) →
  ( exists ℕ (λ n → is-true-Prop (f n))) +
  ( for-all ℕ (λ n → is-false-Prop (f n)))
```

## Properties

### The limited principle of omniscience is a proposition

```agda
is-prop-LPO : is-prop LPO
is-prop-LPO =
  is-prop-Π
    ( λ f →
      is-prop-coproduct
        ( elim-exists
          ( ¬' ∀' ℕ (λ n → is-false-Prop (f n)))
          ( λ n t h → not-is-false-is-true (f n) t (h n)))
        ( is-prop-exists ℕ (λ n → is-true-Prop (f n)))
        ( is-prop-for-all-Prop ℕ (λ n → is-false-Prop (f n))))

prop-LPO : Prop lzero
prop-LPO = LPO , is-prop-LPO
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [Taboos.LPO](https://martinescardo.github.io/TypeTopology/Taboos.LPO.html) at
  TypeTopology
- [limited principle of omniscience](https://ncatlab.org/nlab/show/limited+principle+of+omniscience)
  at $n$Lab
