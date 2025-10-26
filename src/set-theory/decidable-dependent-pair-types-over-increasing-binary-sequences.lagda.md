# Decidability of dependents pair types over increasing binary sequences

```agda
module set-theory.decidable-dependent-pair-types-over-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.logical-operations-booleans
open import foundation.negated-equality
open import foundation.types-with-decidable-dependent-pair-types
open import foundation.types-with-decidable-dependent-product-types

open import foundation-core.identity-types

open import set-theory.inclusion-natural-numbers-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
open import set-theory.shifting-increasing-binary-sequences
```

</details>

## Idea

[Dependent sums](foundation.dependent-pair-types.md) of
[decidable types](foundation.decidable-types.md) over
[increasing binary sequences](set-theory.increasing-binary-sequences.md) are
decidable {{#cite Esc13}}. This is also known as the _compactness_ of the
conatural numbers. The formalization is based on earlier formalizations written
by Martín Escardó {{#cite TypeTopology}}.

We prove that the type of increasing binary sequences "pointedly" has decidable
dependent sums, meaning that for every [boolean](foundation.booleans.md)
predicate `P` on the type of increasing binary sequences, there constructibly
exists an element `σ` such that if `P σ` is false, then `P` is empty. From this
the main result is an easy corollary.

## Lemmas

Given a boolean predicate `P : ℕ∞↗ → bool`, we begin by constructing a new
increasing binary sequence `σ : ℕ∞↗` (in the formalization:
`force-binary-sequence-ℕ∞↗`) given at the n'th position by taking the least
upper bound of the initial segment of `P` up to and including the n'th position:

$$
  σₙ := ⋃ⁿᵢ₌₀ Pᵢ.
$$

Since `σ` is an increasing binary sequence we can ask what the value of `P` is
_at_ `σ`. The lemmas lead up to demonstrating that if `P σ` is false, then `P`
is the constantly false sequence, hence `σ` witnesses our main theorem.

```agda
module _
  (P : ℕ∞↗ → bool)
  where

  force-binary-sequence-ℕ∞↗ : ℕ∞↗
  force-binary-sequence-ℕ∞↗ =
    force-ℕ∞↗ (P ∘ increasing-binary-sequence-ℕ)
```

### Computing `P` under given assumptions on `σ`

If `σ` is equal to an increasing binary sequence `x` shifted over `n` times,
then `P n = x₀`.

```agda
  compute-force-binary-sequence-Eq-shift-ℕ∞↗ :
    (x : ℕ∞↗) (n : ℕ) →
    Eq-ℕ∞↗ force-binary-sequence-ℕ∞↗ (shift-ℕ∞↗ n x) →
    P (increasing-binary-sequence-ℕ n) ＝ sequence-ℕ∞↗ x 0
  compute-force-binary-sequence-Eq-shift-ℕ∞↗
    x 0 r =
    r 0
  compute-force-binary-sequence-Eq-shift-ℕ∞↗
    x (succ-ℕ n) r =
    ( inv
      ( ( ap
          ( or-bool (P (increasing-binary-sequence-ℕ (succ-ℕ n))))
          ( r n ∙ compute-ev-shift-succ-ℕ∞↗ n x)) ∙
        ( right-unit-law-or-bool))) ∙
    ( r (succ-ℕ n)) ∙
    ( compute-ev-shift-ℕ∞↗ (succ-ℕ n) x)

  abstract
    compute-force-binary-sequence-eq-shift-ℕ∞↗ :
      (x : ℕ∞↗) (n : ℕ) →
      force-binary-sequence-ℕ∞↗ ＝ shift-ℕ∞↗ n x →
      P (increasing-binary-sequence-ℕ n) ＝ sequence-ℕ∞↗ x 0
    compute-force-binary-sequence-eq-shift-ℕ∞↗ x n r =
      compute-force-binary-sequence-Eq-shift-ℕ∞↗ x n (Eq-eq-ℕ∞↗ r)
```

If `σ` is a finite number `n`, then `P n` is true.

```agda
  abstract
    compute-force-binary-sequence-eq-increasing-binary-sequence-ℕ :
      (n : ℕ) →
      force-binary-sequence-ℕ∞↗ ＝ increasing-binary-sequence-ℕ n →
      P (increasing-binary-sequence-ℕ n) ＝ true
    compute-force-binary-sequence-eq-increasing-binary-sequence-ℕ n r =
      compute-force-binary-sequence-eq-shift-ℕ∞↗ zero-ℕ∞↗ n
        ( r ∙ inv-compute-shift-zero-ℕ∞↗ n)
```

If `σ` is infinite, then `P n` is false for all `n`.

```agda
  abstract
    compute-force-binary-sequence-eq-infinity-ℕ∞↗ :
      (n : ℕ) →
      force-binary-sequence-ℕ∞↗ ＝ infinity-ℕ∞↗ →
      P (increasing-binary-sequence-ℕ n) ＝ false
    compute-force-binary-sequence-eq-infinity-ℕ∞↗ n r =
      compute-force-binary-sequence-eq-shift-ℕ∞↗ infinity-ℕ∞↗ n
        ( r ∙ inv-compute-shift-infinity-ℕ∞↗ n)
```

### Computing `P` at `σ`

If `σ` is a finite number `n`, then `P σ` is true.

```agda
  abstract
    is-true-ev-force-binary-sequence-eq-increasing-binary-sequence-ℕ :
      (n : ℕ) →
      force-binary-sequence-ℕ∞↗ ＝ increasing-binary-sequence-ℕ n →
      P force-binary-sequence-ℕ∞↗ ＝ true
    is-true-ev-force-binary-sequence-eq-increasing-binary-sequence-ℕ n t =
      ap P t ∙ compute-force-binary-sequence-eq-increasing-binary-sequence-ℕ n t
```

Contrapositively, if `P σ` is false then `σ` is infinite.

```agda
  abstract
    is-not-finite-is-false-ev-force-binary-sequence-ℕ∞↗ :
      P force-binary-sequence-ℕ∞↗ ＝ false →
      (n : ℕ) → force-binary-sequence-ℕ∞↗ ≠ increasing-binary-sequence-ℕ n
    is-not-finite-is-false-ev-force-binary-sequence-ℕ∞↗
      r n s =
      neq-false-true-bool
        ( inv r ∙
          is-true-ev-force-binary-sequence-eq-increasing-binary-sequence-ℕ n s)

    is-infinite-is-false-ev-force-binary-sequence-ℕ∞↗ :
      P force-binary-sequence-ℕ∞↗ ＝ false →
      force-binary-sequence-ℕ∞↗ ＝ infinity-ℕ∞↗
    is-infinite-is-false-ev-force-binary-sequence-ℕ∞↗ r =
      eq-infinity-is-not-in-image-increasing-binary-sequence-ℕ
        ( force-binary-sequence-ℕ∞↗)
        ( is-not-finite-is-false-ev-force-binary-sequence-ℕ∞↗ r)
```

If `P σ` is false, then `P` is always false.

```agda
  abstract
    is-constantly-false-is-false-ev-force-binary-sequence-ℕ∞↗ :
      P force-binary-sequence-ℕ∞↗ ＝ false → (x : ℕ∞↗) → P x ＝ false
    is-constantly-false-is-false-ev-force-binary-sequence-ℕ∞↗ r =
      htpy-ℕ∞↗-htpy-ℕ+∞
        ( λ _ → has-double-negation-stable-equality-bool)
        ( λ n →
          compute-force-binary-sequence-eq-infinity-ℕ∞↗ n
            ( is-infinite-is-false-ev-force-binary-sequence-ℕ∞↗ r))
        ( ap P (inv (is-infinite-is-false-ev-force-binary-sequence-ℕ∞↗ r)) ∙ r)
```

## Theorem

```agda
abstract
  has-decidable-Σ-pointed-bool'-ℕ∞↗ :
    has-decidable-Σ-pointed-bool' ℕ∞↗
  has-decidable-Σ-pointed-bool'-ℕ∞↗ P =
    ( force-binary-sequence-ℕ∞↗ P ,
      is-constantly-false-is-false-ev-force-binary-sequence-ℕ∞↗ P)

  has-decidable-Σ-pointed-bool-ℕ∞↗ :
    has-decidable-Σ-pointed-bool ℕ∞↗
  has-decidable-Σ-pointed-bool-ℕ∞↗ =
    flip-has-decidable-Σ-pointed-bool
      ( has-decidable-Σ-pointed-bool'-ℕ∞↗)

  has-decidable-type-subtype-pointed-ℕ∞↗ :
    has-decidable-type-subtype-pointed ℕ∞↗
  has-decidable-type-subtype-pointed-ℕ∞↗ =
    has-decidable-type-subtype-pointed-has-decidable-Σ-pointed-bool
      ( has-decidable-Σ-pointed-bool-ℕ∞↗)

  has-decidable-Σ-pointed-ℕ∞↗ :
    has-decidable-Σ-pointed ℕ∞↗
  has-decidable-Σ-pointed-ℕ∞↗ =
    has-decidable-Σ-pointed-has-decidable-type-subtype-pointed
      ( has-decidable-type-subtype-pointed-ℕ∞↗)

  has-decidable-Σ-ℕ∞↗ :
    has-decidable-Σ ℕ∞↗
  has-decidable-Σ-ℕ∞↗ =
    has-decidable-Σ-has-decidable-Σ-pointed
      ( has-decidable-Σ-pointed-ℕ∞↗)
```

## Corollaries

### The type of increasing binary sequences has decidable Π-types

```agda
has-decidable-Π-ℕ∞↗ : has-decidable-Π ℕ∞↗
has-decidable-Π-ℕ∞↗ =
  has-decidable-Π-has-decidable-Σ has-decidable-Σ-ℕ∞↗
```

## References

- [`TypeTopology.GenericConvergentSequenceCompactness`](https://martinescardo.github.io/TypeTopology/TypeTopology.GenericConvergentSequenceCompactness.html)
  at TypeTopology {{#cite TypeTopology}}

{{#bibliography}}
