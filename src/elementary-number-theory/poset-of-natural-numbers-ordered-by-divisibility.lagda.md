# The poset of natural numbers ordered by divisibility

```agda
module
  elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

The {{#concept "poset of natural numbers ordered by divisibility" Agda=ℕ-Div-Poset}} consists of the
[natural numbers](elementary-number-theory.natural-numbers.md) and its ordering
is defined by `m ≤ n := m | n`, i.e., by
[divisibility](elementary-number-theory.divisibility-natural-numbers.md).

The divisibility relation `m | n` on the natural numbers, however, is only
valued in the [propositions](foundation.propositions.md) when both `m` and `n`
are [nonzero](elementary-number-theory.nonzero-natural-numbers.md). We therefore
redefine the divisibility relation in the following way: A number `m` is said to
**divide** a number `n` if there
[merely exists](foundation.existential-quantification.md) a number `k` such that
`km ＝ n`. Since mere existence is defined via the
[propoositional truncation](foundation.propositional-truncations.md), this can
be stated alternatively as the proposition

```text
  trunc-Prop (div-ℕ m n).
```

In other words, we simply force the divisibility relation to take values in
propositions by identifying all witnesses of divisibility.

## Definition

```agda
leq-prop-ℕ-Div : ℕ → ℕ → Prop lzero
leq-prop-ℕ-Div m n = trunc-Prop (div-ℕ m n)

leq-ℕ-Div : ℕ → ℕ → UU lzero
leq-ℕ-Div m n = type-Prop (leq-prop-ℕ-Div m n)

refl-leq-ℕ-Div : (n : ℕ) → leq-ℕ-Div n n
refl-leq-ℕ-Div n = unit-trunc-Prop (refl-div-ℕ n)

antisymmetric-leq-ℕ-Div : (m n : ℕ) → leq-ℕ-Div m n → leq-ℕ-Div n m → m ＝ n
antisymmetric-leq-ℕ-Div m n H K =
  apply-twice-universal-property-trunc-Prop H K
    ( Id-Prop ℕ-Set _ _)
    ( antisymmetric-div-ℕ m n)

transitive-leq-ℕ-Div :
  (m n o : ℕ) → leq-ℕ-Div n o → leq-ℕ-Div m n → leq-ℕ-Div m o
transitive-leq-ℕ-Div m n o H K =
  apply-twice-universal-property-trunc-Prop H K
    ( leq-prop-ℕ-Div m o)
    ( λ H' K' → unit-trunc-Prop (transitive-div-ℕ m n o H' K'))

ℕ-Div-Preorder : Preorder lzero lzero
pr1 ℕ-Div-Preorder = ℕ
pr1 (pr2 ℕ-Div-Preorder) = leq-prop-ℕ-Div
pr1 (pr2 (pr2 ℕ-Div-Preorder)) = refl-leq-ℕ-Div
pr2 (pr2 (pr2 ℕ-Div-Preorder)) = transitive-leq-ℕ-Div

ℕ-Div-Poset : Poset lzero lzero
pr1 ℕ-Div-Poset = ℕ-Div-Preorder
pr2 ℕ-Div-Poset = antisymmetric-leq-ℕ-Div
```
