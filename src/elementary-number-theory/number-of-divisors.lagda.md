# The number of divisors function

```agda
module elementary-number-theory.number-of-divisors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.bounded-divisibility-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "number of divisors" Agda=number-of-divisors-ℕ OEIS=A000005 WDID=Q12890701 WD="number of divisors"}}
$\tau(n)$ of a [natural number](elementary-number-theory.natural-numbers.md) $n$
is the number of natural numbers $d \leq n$ that
[divide](elementary-number-theory.divisibility.natural-numbers.md) the number
$n$, i.e.,

$$
  \tau(n) := |\{d \in \mathbb{N} \mid d|n\}|.
$$

The number of divisors function is listed as A000005 in the
[OEIS](literature.oeis.md) {{#cite OEIS}}.

## Definitions

### The type of divisors

```agda
decidable-subtype-of-divisors-ℕ :
  (n : ℕ) → decidable-subtype lzero (Fin (succ-ℕ n))
decidable-subtype-of-divisors-ℕ n i =
  bounded-div-ℕ-Decidable-Prop (nat-Fin (succ-ℕ n) i) n

type-of-divisors-ℕ : ℕ → UU lzero
type-of-divisors-ℕ n =
  type-decidable-subtype (decidable-subtype-of-divisors-ℕ n)

quotient-type-of-divisors-ℕ :
  (n : ℕ) → type-of-divisors-ℕ n → type-of-divisors-ℕ n
pr1 (quotient-type-of-divisors-ℕ n (d , H)) =
  mod-succ-ℕ n (quotient-bounded-div-ℕ (nat-Fin (succ-ℕ n) d) n H)
pr1 (pr2 (quotient-type-of-divisors-ℕ n (d , H))) =
  nat-Fin (succ-ℕ n) d
pr1 (pr2 (pr2 (quotient-type-of-divisors-ℕ n (d , H)))) =
  upper-bound-nat-Fin n d
pr2 (pr2 (pr2 (quotient-type-of-divisors-ℕ n (d , H)))) =
  {!is-section-nat-Fin n!}
```

### The number of divisors function

Note that the entry `number-of-elements-decidable-subtype` refers to
`count-decidable-subtype'`, which is `abstract` and therefore doesn't compute.

```agda
count-type-of-divisors-ℕ :
  (n : ℕ) → count (type-of-divisors-ℕ n)
count-type-of-divisors-ℕ n =
  count-decidable-subtype
    ( decidable-subtype-of-divisors-ℕ n)
    ( count-Fin (succ-ℕ n))

number-of-divisors-ℕ : ℕ → ℕ
number-of-divisors-ℕ n =
  number-of-elements-decidable-subtype
    ( decidable-subtype-of-divisors-ℕ n)
    ( count-Fin (succ-ℕ n))
```

### Involution on the type of divisors

For every natural number `n : ℕ`, the map `d ↦ n/d` mapping a divisor of `n` to
its quotient is an involution. This operation has a fixed point precisely when
`n` is a [square number](elementary-number-theory.square-natural-numbers.md).

```agda

```
