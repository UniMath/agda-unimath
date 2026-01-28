# The classical intermediate value theorem

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.classical-intermediate-value-theorem where
```

<details><summary>Imports</summary>

```agda
open import real-numbers.closed-intervals-real-numbers
open import foundation.dependent-pair-types
open import lists.sequences
open import real-numbers.binary-mean-real-numbers
open import foundation.homotopies
open import foundation.propositional-truncations
open import elementary-number-theory.addition-positive-rational-numbers
open import real-numbers.iterated-halving-difference-real-numbers
open import foundation.coproduct-types
open import real-numbers.rational-real-numbers
open import real-numbers.dedekind-real-numbers
open import foundation.law-of-excluded-middle
open import elementary-number-theory.natural-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.negation-real-numbers
open import foundation.identity-types
open import foundation.universe-levels
open import real-numbers.nonpositive-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.positive-real-numbers
open import foundation.empty-types
open import real-numbers.increasing-sequences-real-numbers
open import real-numbers.limits-of-sequences-real-numbers
open import real-numbers.cauchy-sequences-real-numbers
open import real-numbers.real-sequences-approximating-zero
open import real-numbers.decreasing-sequences-real-numbers
open import real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers
```

</details>

## Idea

The
{{#concept "classical intermediate value theorem" WDID=Q245098 WD="intermediate value theorem"}}
states that for a
[pointwise ε-δ continuous endomap](real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers.md)
`f` on the [real numbers](real-numbers.dedekind-real-numbers.md), real numbers
`a` and `b` with `a`
[less than or equal to](real-numbers.inequality-real-numbers.md) `b` such that
`f a` is [negative](real-numbers.negative-real-numbers.md) and `f b` is
[positive](real-numbers.positive-real-numbers.md), there exists a `c` with
`a ≤ c ≤ b` such that `f c` is zero.

$n$Lab states that this theorem is known to be invalid in constructive contexts.

This contrasts with the
[constructive intermediate value theorem](analysis.intermediate-value-theorem.md),
which states merely that for any
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
there exists a `c` with `a ≤ c ≤ b` with `|f c| ≤ ε`.

## Proof

```agda
module _
  {l1 l2 : Level}
  (lem : level-LEM l2)
  (f : pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l1 l1)
  (fa≤0 : is-nonpositive-ℝ (map-pointwise-ε-δ-continuous-endomap-ℝ f a))
  (0≤fb : is-nonnegative-ℝ (map-pointwise-ε-δ-continuous-endomap-ℝ f b))
  where

  interleaved mutual
    lower-bound-sequence-classical-intermediate-value-theorem-ℝ :
      sequence (ℝ l1)
    upper-bound-sequence-classical-intermediate-value-theorem-ℝ :
      sequence (ℝ l1)
    sequence-classical-intermediate-value-theorem-ℝ : sequence (ℝ l1)

    sequence-classical-intermediate-value-theorem-ℝ n =
      binary-mean-ℝ
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n)

    lower-bound-sequence-classical-intermediate-value-theorem-ℝ 0 = a
    lower-bound-sequence-classical-intermediate-value-theorem-ℝ (succ-ℕ n) =
      rec-coproduct
        ( λ _ → sequence-classical-intermediate-value-theorem-ℝ n)
        ( λ _ → lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( linear-leq-lem-ℝ
          ( lem)
          ( map-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( sequence-classical-intermediate-value-theorem-ℝ n))
          ( zero-ℝ))

    upper-bound-sequence-classical-intermediate-value-theorem-ℝ 0 = b
    upper-bound-sequence-classical-intermediate-value-theorem-ℝ (succ-ℕ n) =
      rec-coproduct
        ( λ _ → upper-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( λ _ → sequence-classical-intermediate-value-theorem-ℝ n)
        ( linear-leq-lem-ℝ
          ( lem)
          ( map-pointwise-ε-δ-continuous-endomap-ℝ
            ( f)
            ( sequence-classical-intermediate-value-theorem-ℝ n))
          ( zero-ℝ))
```

### `aₙ ≤ cₙ ≤ bₙ`

```agda
  abstract interleaved mutual
    leq-lower-upper-bound-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n)

    leq-lower-bound-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( sequence-classical-intermediate-value-theorem-ℝ n)

    leq-upper-bound-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( sequence-classical-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n)

    sign-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      ( is-nonpositive-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( sequence-classical-intermediate-value-theorem-ℝ n))) +
      ( is-nonnegative-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( sequence-classical-intermediate-value-theorem-ℝ n)))

    sign-sequence-classical-intermediate-value-theorem-ℝ n =
      linear-leq-lem-ℝ
        ( lem)
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( sequence-classical-intermediate-value-theorem-ℝ n))
        ( zero-ℝ)

    leq-lower-upper-bound-sequence-classical-intermediate-value-theorem-ℝ 0 =
      a≤b
    leq-lower-upper-bound-sequence-classical-intermediate-value-theorem-ℝ
      (succ-ℕ n)
      with sign-sequence-classical-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 =
      leq-upper-bound-sequence-classical-intermediate-value-theorem-ℝ n
    ... | inr 0≤fcₙ =
      leq-lower-bound-sequence-classical-intermediate-value-theorem-ℝ n

    leq-lower-bound-sequence-classical-intermediate-value-theorem-ℝ n =
      leq-binary-mean-leq-both-ℝ
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( refl-leq-ℝ _)
        ( leq-lower-upper-bound-sequence-classical-intermediate-value-theorem-ℝ
          ( n))

    leq-upper-bound-sequence-classical-intermediate-value-theorem-ℝ n =
      geq-binary-mean-geq-both-ℝ
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( leq-lower-upper-bound-sequence-classical-intermediate-value-theorem-ℝ
          ( n))
        ( refl-leq-ℝ _)
```

### `f aₙ ≤ 0`

```agda
  abstract
    is-nonpositive-map-lower-bound-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      is-nonpositive-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n))
    is-nonpositive-map-lower-bound-sequence-classical-intermediate-value-theorem-ℝ
      0 =
      fa≤0
    is-nonpositive-map-lower-bound-sequence-classical-intermediate-value-theorem-ℝ
      (succ-ℕ n)
      with sign-sequence-classical-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 = fcₙ≤0
    ... | inr 0≤fcₙ =
      is-nonpositive-map-lower-bound-sequence-classical-intermediate-value-theorem-ℝ
        ( n)
```

### `0 ≤ f bₙ`

```agda
  abstract
    is-nonnegative-map-upper-bound-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      is-nonnegative-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n))
    is-nonnegative-map-upper-bound-sequence-classical-intermediate-value-theorem-ℝ
      0 =
      0≤fb
    is-nonnegative-map-upper-bound-sequence-classical-intermediate-value-theorem-ℝ
      (succ-ℕ n) with sign-sequence-classical-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 =
      is-nonnegative-map-upper-bound-sequence-classical-intermediate-value-theorem-ℝ
        ( n)
    ... | inr 0≤fcₙ = 0≤fcₙ
```

### `bₙ - aₙ = (b-a)/2ⁿ`

```agda
  abstract interleaved mutual
    diff-upper-lower-bound-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      ( ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n) -ℝ
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)) ＝
      iterated-half-diff-leq-ℝ a≤b n

    diff-upper-bound-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      ( ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n) -ℝ
        ( sequence-classical-intermediate-value-theorem-ℝ n)) ＝
      iterated-half-diff-leq-ℝ a≤b (succ-ℕ n)

    diff-lower-bound-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      ( ( sequence-classical-intermediate-value-theorem-ℝ n) -ℝ
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)) ＝
      iterated-half-diff-leq-ℝ a≤b (succ-ℕ n)

    diff-upper-lower-bound-sequence-classical-intermediate-value-theorem-ℝ 0 =
      inv (right-unit-law-mul-ℝ _)
    diff-upper-lower-bound-sequence-classical-intermediate-value-theorem-ℝ
      (succ-ℕ n) with sign-sequence-classical-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 =
      diff-upper-bound-sequence-classical-intermediate-value-theorem-ℝ n
    ... | inr 0≤fcₙ =
      diff-lower-bound-sequence-classical-intermediate-value-theorem-ℝ n

    diff-upper-bound-sequence-classical-intermediate-value-theorem-ℝ n =
      equational-reasoning
        upper-bound-sequence-classical-intermediate-value-theorem-ℝ n -ℝ
        sequence-classical-intermediate-value-theorem-ℝ n
        ＝
          binary-mean-ℝ
            ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n)
            ( neg-ℝ
              ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n))
          by diff-right-binary-mean-ℝ _ _
        ＝ one-half-ℝ *ℝ iterated-half-diff-leq-ℝ a≤b n
          by
            ap-mul-ℝ
              ( refl {x = one-half-ℝ})
              ( diff-upper-lower-bound-sequence-classical-intermediate-value-theorem-ℝ
                ( n))
        ＝ iterated-half-diff-leq-ℝ a≤b (succ-ℕ n)
          by mul-one-half-iterated-half-diff-leq-ℝ a≤b n

    diff-lower-bound-sequence-classical-intermediate-value-theorem-ℝ n =
      equational-reasoning
        sequence-classical-intermediate-value-theorem-ℝ n -ℝ
        lower-bound-sequence-classical-intermediate-value-theorem-ℝ n
        ＝
          binary-mean-ℝ
            ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n)
            ( neg-ℝ
              ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n))
          by diff-left-binary-mean-ℝ _ _
        ＝ one-half-ℝ *ℝ iterated-half-diff-leq-ℝ a≤b n
          by
            ap-mul-ℝ
              ( refl {x = one-half-ℝ})
              ( diff-upper-lower-bound-sequence-classical-intermediate-value-theorem-ℝ
                ( n))
        ＝ iterated-half-diff-leq-ℝ a≤b (succ-ℕ n)
          by mul-one-half-iterated-half-diff-leq-ℝ a≤b n
```

### The sequence `aₙ` is increasing

```agda
  abstract
    leq-succ-lower-bound-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ
          ( succ-ℕ n))
    leq-succ-lower-bound-sequence-classical-intermediate-value-theorem-ℝ n
      with sign-sequence-classical-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 =
      leq-lower-bound-sequence-classical-intermediate-value-theorem-ℝ n
    ... | inr 0≤fcₙ = refl-leq-ℝ _

    is-increasing-lower-bound-sequence-classical-intermediate-value-theorem-ℝ :
      is-increasing-sequence-ℝ
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ)
    is-increasing-lower-bound-sequence-classical-intermediate-value-theorem-ℝ =
      is-increasing-leq-succ-sequence-ℝ _
        ( leq-succ-lower-bound-sequence-classical-intermediate-value-theorem-ℝ)
```

### The sequence `bₙ` is decreasing

```agda
  abstract
    leq-succ-upper-bound-sequence-classical-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ
          ( succ-ℕ n))
        ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ n)
    leq-succ-upper-bound-sequence-classical-intermediate-value-theorem-ℝ n
      with sign-sequence-classical-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 = refl-leq-ℝ _
    ... | inr 0≤fcₙ =
      leq-upper-bound-sequence-classical-intermediate-value-theorem-ℝ n

    is-decreasing-upper-bound-sequence-classical-intermediate-value-theorem-ℝ :
      is-decreasing-sequence-ℝ
        ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ)
    is-decreasing-upper-bound-sequence-classical-intermediate-value-theorem-ℝ =
      is-decreasing-leq-succ-sequence-ℝ _
        ( leq-succ-upper-bound-sequence-classical-intermediate-value-theorem-ℝ)
```

### The sequence `cₙ` is Cauchy

```agda
  abstract
    is-cauchy-sequence-classical-intermediate-value-theorem-ℝ :
      is-cauchy-sequence-ℝ sequence-classical-intermediate-value-theorem-ℝ
    is-cauchy-sequence-classical-intermediate-value-theorem-ℝ =
      is-cauchy-squeeze-theorem-sequence-ℝ
        ( lower-bound-sequence-classical-intermediate-value-theorem-ℝ)
        ( sequence-classical-intermediate-value-theorem-ℝ)
        ( upper-bound-sequence-classical-intermediate-value-theorem-ℝ)
        ( leq-lower-bound-sequence-classical-intermediate-value-theorem-ℝ)
        ( leq-upper-bound-sequence-classical-intermediate-value-theorem-ℝ)
        ( is-increasing-lower-bound-sequence-classical-intermediate-value-theorem-ℝ)
        ( is-decreasing-upper-bound-sequence-classical-intermediate-value-theorem-ℝ)
        ( preserves-is-zero-limit-htpy-sequence-ℝ
          ( inv-htpy
            ( diff-upper-lower-bound-sequence-classical-intermediate-value-theorem-ℝ))
          ( is-zero-limit-iterated-half-diff-leq-ℝ a≤b))

    has-limit-sequence-classical-intermediate-value-theorem-ℝ :
      has-limit-sequence-ℝ sequence-classical-intermediate-value-theorem-ℝ
    has-limit-sequence-classical-intermediate-value-theorem-ℝ =
      has-limit-cauchy-sequence-ℝ
        ( sequence-classical-intermediate-value-theorem-ℝ ,
          is-cauchy-sequence-classical-intermediate-value-theorem-ℝ)

  limit-sequence-classical-intermediate-value-theorem-ℝ : ℝ l1
  limit-sequence-classical-intermediate-value-theorem-ℝ =
    pr1 has-limit-sequence-classical-intermediate-value-theorem-ℝ

  is-limit-sequence-classical-intermediate-value-theorem-ℝ :
    is-limit-sequence-ℝ
      ( sequence-classical-intermediate-value-theorem-ℝ)
      ( limit-sequence-classical-intermediate-value-theorem-ℝ)
  is-limit-sequence-classical-intermediate-value-theorem-ℝ =
    pr2 has-limit-sequence-classical-intermediate-value-theorem-ℝ
```

### `a ≤ c ≤ b`

```agda
  abstract
    leq-lower-bound-lim-sequence-classical-intermediate-value-theorem-ℝ :
      leq-ℝ a limit-sequence-classical-intermediate-value-theorem-ℝ
    leq-lower-bound-lim-sequence-classical-intermediate-value-theorem-ℝ =
      lower-bound-lim-lower-bound-sequence-ℝ
        ( a)
        ( λ n →
          transitive-leq-ℝ _ _ _
            ( leq-lower-bound-sequence-classical-intermediate-value-theorem-ℝ n)
            ( is-increasing-lower-bound-sequence-classical-intermediate-value-theorem-ℝ
              ( 0)
              ( n)
              ( _)))
        ( is-limit-sequence-classical-intermediate-value-theorem-ℝ)

    leq-upper-bound-lim-sequence-classical-intermediate-value-theorem-ℝ :
      leq-ℝ limit-sequence-classical-intermediate-value-theorem-ℝ b
    leq-upper-bound-lim-sequence-classical-intermediate-value-theorem-ℝ =
      upper-bound-lim-upper-bound-sequence-ℝ
        ( b)
        ( λ n →
          transitive-leq-ℝ _ _ _
            ( is-decreasing-upper-bound-sequence-classical-intermediate-value-theorem-ℝ
              ( 0)
              ( n)
              ( _))
            ( leq-upper-bound-sequence-classical-intermediate-value-theorem-ℝ
              ( n)))
        ( is-limit-sequence-classical-intermediate-value-theorem-ℝ)
```

### `f c ≤ 0`

```agda
  abstract
    is-nonpositive-map-limit-sequence-classical-intermediate-value-theorem-ℝ :
      is-nonpositive-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( limit-sequence-classical-intermediate-value-theorem-ℝ))
    is-nonpositive-map-limit-sequence-classical-intermediate-value-theorem-ℝ =
      leq-not-le-ℝ _ _
        ( λ 0<fc →
          let open do-syntax-trunc-Prop empty-Prop
          in do
            (ε , ε<fc) ← exists-ℚ⁺-in-lower-cut-ℝ⁺ (_ , 0<fc)
            let (
            {!   !})
```

## External links

- [Intermediate value theorem](https://ncatlab.org/nlab/show/intermediate+value+theorem)
  on $n$Lab
- [Intermediate value theorem](https://en.wikipedia.org/wiki/Intermediate_value_theorem)
  on Wikipedia
