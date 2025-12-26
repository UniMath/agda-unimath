# The intermediate value theorem

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.intermediate-value-theorem where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-positive-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences
open import lists.subsequences

open import logic.functoriality-existential-quantification

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.binary-mean-real-numbers
open import real-numbers.cauchy-sequences-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.decreasing-sequences-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.increasing-sequences-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.limits-sequences-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.pointwise-continuous-functions-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-sequences-approximating-zero
open import real-numbers.similarity-nonnegative-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "constructive intermediate value theorem" Agda=intermediate-value-theorem-ℝ}}
states that for a
[pointwise continuous function](real-numbers.pointwise-continuous-functions-real-numbers.md)
`f` from the [real numbers](real-numbers.dedekind-real-numbers.md) to
themselves, real numbers `a` and `b` with `a`
[less than or equal to](real-numbers.inequality-real-numbers.md) `b` such that
`f a` is [negative](real-numbers.negative-real-numbers.md) and `f b` is
[positive](real-numbers.positive-real-numbers.md), and a
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
there exists a `c` with `a ≤ c ≤ b` such that the
[absolute value](real-numbers.absolute-value-real-numbers.md) of `f c` is at
most `ε`.

The
[classical intermediate value theorem](analysis.classical-intermediate-value-theorem.md)
is the [79th](literature.100-theorems.md#79) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Proof

This proof is adapted from {{#cite Frank2020}}.

### Defining the sequences `aₙ`, `bₙ`, `cₙ`

```agda
module _
  {l : Level}
  (f : pointwise-continuous-map-ℝ l l)
  (a b : ℝ l)
  (a≤b : leq-ℝ a b)
  (fa<0 : is-negative-ℝ (map-pointwise-continuous-map-ℝ f a))
  (0<fb : is-positive-ℝ (map-pointwise-continuous-map-ℝ f b))
  (ε : ℚ⁺)
  where

  interleaved mutual
    lower-bound-seq-intermediate-value-theorem-ℝ : sequence (ℝ l)

    upper-bound-seq-intermediate-value-theorem-ℝ : sequence (ℝ l)

    seq-intermediate-value-theorem-ℝ : sequence (ℝ l)

    seq-intermediate-value-theorem-ℝ n =
      binary-mean-ℝ
        ( lower-bound-seq-intermediate-value-theorem-ℝ n)
        ( upper-bound-seq-intermediate-value-theorem-ℝ n)

    interpolation-seq-intermediate-value-theorem-ℝ :
      sequence (type-closed-interval-ℝ l unit-closed-interval-ℝ)
    interpolation-seq-intermediate-value-theorem-ℝ n =
      clamp-closed-interval-ℝ
        ( unit-closed-interval-ℝ)
        ( ( one-half-ℝ) +ℝ
          ( ( map-pointwise-continuous-map-ℝ
              ( f)
              ( seq-intermediate-value-theorem-ℝ n)) *ℝ
            ( real-ℚ⁺ (inv-ℚ⁺ ε))))

    shift-seq-intermediate-value-theorem-ℝ : sequence (ℝ⁰⁺ l)
    shift-seq-intermediate-value-theorem-ℝ n =
      let
        (d , 0≤d , _) = interpolation-seq-intermediate-value-theorem-ℝ n
      in
        ( d , 0≤d) *ℝ⁰⁺
        ( ( nonnegative-diff-leq-ℝ a≤b) *ℝ⁰⁺
          ( nonnegative-real-ℚ⁺ (power-ℚ⁺ (succ-ℕ n) one-half-ℚ⁺)))

    lower-bound-seq-intermediate-value-theorem-ℝ 0 = a
    lower-bound-seq-intermediate-value-theorem-ℝ (succ-ℕ n) =
      ( seq-intermediate-value-theorem-ℝ n) -ℝ
      ( real-ℝ⁰⁺ (shift-seq-intermediate-value-theorem-ℝ n))

    upper-bound-seq-intermediate-value-theorem-ℝ 0 = b
    upper-bound-seq-intermediate-value-theorem-ℝ (succ-ℕ n) =
      ( upper-bound-seq-intermediate-value-theorem-ℝ n) -ℝ
      ( real-ℝ⁰⁺ (shift-seq-intermediate-value-theorem-ℝ n))
```

### `aₙ ≤ cₙ ≤ bₙ`

```agda
  interleaved mutual
    leq-lower-upper-bound-sequence-intermediate-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( lower-bound-seq-intermediate-value-theorem-ℝ n)
        ( upper-bound-seq-intermediate-value-theorem-ℝ n)

    is-lower-bound-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( lower-bound-seq-intermediate-value-theorem-ℝ n)
        ( seq-intermediate-value-theorem-ℝ n)
    is-lower-bound-seq-intermediate-value-theorem-ℝ n =
      leq-binary-mean-leq-both-ℝ _ _ _
        ( refl-leq-ℝ (lower-bound-seq-intermediate-value-theorem-ℝ n))
        ( leq-lower-upper-bound-sequence-intermediate-theorem-ℝ n)

    is-upper-bound-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( seq-intermediate-value-theorem-ℝ n)
        ( upper-bound-seq-intermediate-value-theorem-ℝ n)
    is-upper-bound-seq-intermediate-value-theorem-ℝ n =
      geq-binary-mean-geq-both-ℝ _ _ _
        ( leq-lower-upper-bound-sequence-intermediate-theorem-ℝ n)
        ( refl-leq-ℝ (upper-bound-seq-intermediate-value-theorem-ℝ n))

    leq-lower-upper-bound-sequence-intermediate-theorem-ℝ 0 = a≤b
    leq-lower-upper-bound-sequence-intermediate-theorem-ℝ (succ-ℕ n) =
      preserves-leq-right-add-ℝ _ _ _
        ( is-upper-bound-seq-intermediate-value-theorem-ℝ n)
```

### `bₙ - aₙ = (b - a)/2ⁿ`

```agda
  private
    ⟨b-a⟩/2^ : ℕ → ℝ⁰⁺ l
    ⟨b-a⟩/2^ n =
      nonnegative-diff-leq-ℝ a≤b *ℝ⁰⁺
      nonnegative-real-ℚ⁺ (power-ℚ⁺ n one-half-ℚ⁺)

    ⟨b-a⟩/2^1+ : ℕ → ℝ⁰⁺ l
    ⟨b-a⟩/2^1+ n = ⟨b-a⟩/2^ (succ-ℕ n)

  abstract
    interleaved mutual
      diff-upper-lower-bound-seq-intermediate-value-theorem-ℝ :
        (n : ℕ) →
        ( ( upper-bound-seq-intermediate-value-theorem-ℝ n) -ℝ
          ( lower-bound-seq-intermediate-value-theorem-ℝ n)) ＝
        ( (b -ℝ a) *ℝ real-ℚ⁺ (power-ℚ⁺ n one-half-ℚ⁺))

      diff-upper-bound-seq-intermediate-value-theorem-ℝ :
        (n : ℕ) →
        ( ( upper-bound-seq-intermediate-value-theorem-ℝ n) -ℝ
          ( seq-intermediate-value-theorem-ℝ n)) ＝
        ( (b -ℝ a) *ℝ real-ℚ⁺ (power-ℚ⁺ (succ-ℕ n) one-half-ℚ⁺))

      diff-upper-lower-bound-seq-intermediate-value-theorem-ℝ 0 =
        inv (right-unit-law-mul-ℝ (b -ℝ a))
      diff-upper-lower-bound-seq-intermediate-value-theorem-ℝ (succ-ℕ n) =
        ( eq-sim-ℝ
          ( diff-diff-ℝ
            ( upper-bound-seq-intermediate-value-theorem-ℝ n)
            ( seq-intermediate-value-theorem-ℝ n)
            ( real-ℝ⁰⁺ (shift-seq-intermediate-value-theorem-ℝ n)))) ∙
        ( diff-upper-bound-seq-intermediate-value-theorem-ℝ n)

      diff-upper-bound-seq-intermediate-value-theorem-ℝ n =
        equational-reasoning
          ( upper-bound-seq-intermediate-value-theorem-ℝ n) -ℝ
          ( seq-intermediate-value-theorem-ℝ n)
          ＝
            binary-mean-ℝ
              ( upper-bound-seq-intermediate-value-theorem-ℝ n)
              ( neg-ℝ (lower-bound-seq-intermediate-value-theorem-ℝ n))
            by diff-right-binary-mean-ℝ _ _
          ＝ one-half-ℝ *ℝ real-ℝ⁰⁺ (⟨b-a⟩/2^ n)
            by
              ap-mul-ℝ
                ( refl {x = one-half-ℝ})
                ( diff-upper-lower-bound-seq-intermediate-value-theorem-ℝ
                  ( n))
          ＝
            ( b -ℝ a) *ℝ
            ( one-half-ℝ *ℝ real-ℚ (rational-power-ℚ⁺ n one-half-ℚ⁺))
            by left-swap-mul-ℝ one-half-ℝ (b -ℝ a) _
          ＝ (b -ℝ a) *ℝ real-ℚ (one-half-ℚ *ℚ rational-power-ℚ⁺ n one-half-ℚ⁺)
            by ap-mul-ℝ refl (mul-real-ℚ _ _)
          ＝ real-ℝ⁰⁺ (⟨b-a⟩/2^1+ n)
            by ap-mul-ℝ refl (ap real-ℚ⁺ (inv (power-succ-ℚ⁺' n one-half-ℚ⁺)))

  abstract
    diff-lower-bound-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      ( ( seq-intermediate-value-theorem-ℝ n) -ℝ
        ( lower-bound-seq-intermediate-value-theorem-ℝ n)) ＝
      ( (b -ℝ a) *ℝ real-ℚ⁺ (power-ℚ⁺ (succ-ℕ n) one-half-ℚ⁺))
    diff-lower-bound-seq-intermediate-value-theorem-ℝ n =
      ( diff-left-binary-mean-ℝ _ _) ∙
      ( inv (diff-right-binary-mean-ℝ _ _)) ∙
      ( diff-upper-bound-seq-intermediate-value-theorem-ℝ n)
```

### `aₙ` is increasing

```agda
  abstract
    is-increasing-lower-bound-seq-intermediate-value-theorem-ℝ :
      is-increasing-sequence-ℝ
        ( lower-bound-seq-intermediate-value-theorem-ℝ)
    is-increasing-lower-bound-seq-intermediate-value-theorem-ℝ =
      is-increasing-leq-succ-sequence-ℝ
        ( lower-bound-seq-intermediate-value-theorem-ℝ)
        ( λ n →
          let
            open inequality-reasoning-Large-Poset ℝ-Large-Poset
            (d , 0≤d , d≤1) =
              interpolation-seq-intermediate-value-theorem-ℝ n
          in
            chain-of-inequalities
            lower-bound-seq-intermediate-value-theorem-ℝ n
            ≤ ( seq-intermediate-value-theorem-ℝ n) -ℝ
              ( ( seq-intermediate-value-theorem-ℝ n) -ℝ
                ( lower-bound-seq-intermediate-value-theorem-ℝ n))
              by leq-sim-ℝ (symmetric-sim-ℝ (right-diff-diff-ℝ _ _))
            ≤ ( seq-intermediate-value-theorem-ℝ n) -ℝ
              ( ( b -ℝ a) *ℝ real-ℚ⁺ (power-ℚ⁺ (succ-ℕ n) one-half-ℚ⁺))
              by
                leq-eq-ℝ
                  ( ap-diff-ℝ
                    ( refl)
                    ( diff-lower-bound-seq-intermediate-value-theorem-ℝ n))
            ≤ ( seq-intermediate-value-theorem-ℝ n) -ℝ
              ( real-ℝ⁰⁺ (shift-seq-intermediate-value-theorem-ℝ n))
              by
                preserves-leq-left-add-ℝ _ _ _
                  ( neg-leq-ℝ
                    ( leq-left-mul-leq-one-ℝ⁰⁺
                      ( d , 0≤d)
                      ( ( nonnegative-diff-leq-ℝ a≤b) *ℝ⁰⁺
                        ( nonnegative-real-ℚ⁺
                          ( power-ℚ⁺ (succ-ℕ n) one-half-ℚ⁺)))
                      ( d≤1))))
```

### `bₙ` is decreasing

```agda
  abstract
    is-decreasing-upper-bound-seq-intermediate-value-theorem-ℝ :
      is-decreasing-sequence-ℝ
        ( upper-bound-seq-intermediate-value-theorem-ℝ)
    is-decreasing-upper-bound-seq-intermediate-value-theorem-ℝ =
      is-decreasing-leq-succ-sequence-ℝ
        ( upper-bound-seq-intermediate-value-theorem-ℝ)
        ( λ n →
          leq-diff-real-ℝ⁰⁺
            ( upper-bound-seq-intermediate-value-theorem-ℝ n)
            ( shift-seq-intermediate-value-theorem-ℝ n))
```

### `a ≤ cₙ ≤ b`

```agda
  abstract
    lower-bound-of-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) → leq-ℝ a (seq-intermediate-value-theorem-ℝ n)
    lower-bound-of-seq-intermediate-value-theorem-ℝ n =
      transitive-leq-ℝ
        ( a)
        ( lower-bound-seq-intermediate-value-theorem-ℝ n)
        ( seq-intermediate-value-theorem-ℝ n)
        ( is-lower-bound-seq-intermediate-value-theorem-ℝ n)
        ( is-increasing-lower-bound-seq-intermediate-value-theorem-ℝ
          ( 0)
          ( n)
          ( leq-zero-ℕ n))

    upper-bound-of-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) → leq-ℝ (seq-intermediate-value-theorem-ℝ n) b
    upper-bound-of-seq-intermediate-value-theorem-ℝ n =
      transitive-leq-ℝ
        ( seq-intermediate-value-theorem-ℝ n)
        ( upper-bound-seq-intermediate-value-theorem-ℝ n)
        ( b)
        ( is-decreasing-upper-bound-seq-intermediate-value-theorem-ℝ
          ( 0)
          ( n)
          ( leq-zero-ℕ n))
        ( is-upper-bound-seq-intermediate-value-theorem-ℝ n)
```

### The `cₙ` are a Cauchy sequence with a limit `c`

```agda
  private abstract
    is-zero-limit-⟨b-a⟩/2^ :
      is-zero-limit-sequence-ℝ (real-ℝ⁰⁺ ∘ ⟨b-a⟩/2^)
    is-zero-limit-⟨b-a⟩/2^ =
      preserves-is-zero-limit-left-mul-sequence-ℝ
        ( b -ℝ a)
        ( _)
        ( is-zero-limit-real-is-zero-limit-sequence-ℚ _
          ( is-zero-limit-power-le-one-ℚ⁺
            ( one-half-ℚ⁺)
            ( le-one-half-one-ℚ)))

    is-zero-limit-⟨b-a⟩/2^1+ :
      is-zero-limit-sequence-ℝ (real-ℝ⁰⁺ ∘ ⟨b-a⟩/2^1+)
    is-zero-limit-⟨b-a⟩/2^1+ =
      preserves-is-limit-subsequence-ℝ
        ( tail-subsequence (real-ℝ⁰⁺ ∘ ⟨b-a⟩/2^))
        ( is-zero-limit-⟨b-a⟩/2^)

  abstract
    is-zero-limit-diff-upper-lower-bound-seq-intermediate-value-theorem-ℝ :
      is-zero-limit-sequence-ℝ
        ( λ n →
          ( upper-bound-seq-intermediate-value-theorem-ℝ n) -ℝ
          ( lower-bound-seq-intermediate-value-theorem-ℝ n))
    is-zero-limit-diff-upper-lower-bound-seq-intermediate-value-theorem-ℝ =
      preserves-is-zero-limit-htpy-sequence-ℝ
        ( inv-htpy diff-upper-lower-bound-seq-intermediate-value-theorem-ℝ)
        ( is-zero-limit-⟨b-a⟩/2^)

    has-limit-seq-intermediate-value-theorem-ℝ :
      has-limit-sequence-ℝ seq-intermediate-value-theorem-ℝ
    has-limit-seq-intermediate-value-theorem-ℝ =
      rec-trunc-Prop
        ( has-limit-prop-sequence-ℝ seq-intermediate-value-theorem-ℝ)
        ( λ μ →
          has-limit-cauchy-sequence-ℝ (seq-intermediate-value-theorem-ℝ , μ))
        ( exists-cauchy-modulus-narrowing-bounds-sequence-ℝ
          ( lower-bound-seq-intermediate-value-theorem-ℝ)
          ( seq-intermediate-value-theorem-ℝ)
          ( upper-bound-seq-intermediate-value-theorem-ℝ)
          ( is-lower-bound-seq-intermediate-value-theorem-ℝ)
          ( is-upper-bound-seq-intermediate-value-theorem-ℝ)
          ( is-increasing-lower-bound-seq-intermediate-value-theorem-ℝ)
          ( is-decreasing-upper-bound-seq-intermediate-value-theorem-ℝ)
          ( is-zero-limit-diff-upper-lower-bound-seq-intermediate-value-theorem-ℝ))

  lim-seq-intermediate-value-theorem-ℝ : ℝ l
  lim-seq-intermediate-value-theorem-ℝ =
    pr1 has-limit-seq-intermediate-value-theorem-ℝ

  is-limit-lim-seq-intermediate-value-theorem-ℝ :
    is-limit-sequence-ℝ
      ( seq-intermediate-value-theorem-ℝ)
      ( lim-seq-intermediate-value-theorem-ℝ)
  is-limit-lim-seq-intermediate-value-theorem-ℝ =
    pr2 has-limit-seq-intermediate-value-theorem-ℝ
```

### `a ≤ c ≤ b`

```agda
  abstract
    lower-bound-lim-seq-intermediate-value-theorem-ℝ :
      leq-ℝ a lim-seq-intermediate-value-theorem-ℝ
    lower-bound-lim-seq-intermediate-value-theorem-ℝ =
      lower-bound-lim-lower-bound-sequence-ℝ
        ( a)
        ( lower-bound-of-seq-intermediate-value-theorem-ℝ)
        ( is-limit-lim-seq-intermediate-value-theorem-ℝ)

    upper-bound-lim-seq-intermediate-value-theorem-ℝ :
      leq-ℝ lim-seq-intermediate-value-theorem-ℝ b
    upper-bound-lim-seq-intermediate-value-theorem-ℝ =
      upper-bound-lim-upper-bound-sequence-ℝ
        ( b)
        ( upper-bound-of-seq-intermediate-value-theorem-ℝ)
        ( is-limit-lim-seq-intermediate-value-theorem-ℝ)
```

### If `ε/2 ≤ f cₙ`, then `aₙ₊₁ = aₙ` and `bₙ₊₁ = cₙ`

```agda
  abstract
    sim-one-interpolation-seq-leq-half-ε-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( real-ℚ⁺ (one-half-ℚ⁺ *ℚ⁺ ε))
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( seq-intermediate-value-theorem-ℝ n)) →
      sim-ℝ
        ( pr1 (interpolation-seq-intermediate-value-theorem-ℝ n))
        ( one-ℝ)
    sim-one-interpolation-seq-leq-half-ε-seq-intermediate-value-theorem-ℝ
      n ε/2≤fcₙ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        ε' = one-half-ℚ⁺ *ℚ⁺ ε
        fcₙ =
          map-pointwise-continuous-map-ℝ f (seq-intermediate-value-theorem-ℝ n)
      in
        clamp-leq-upper-bound-closed-interval-ℝ
          ( unit-closed-interval-ℝ)
          ( one-half-ℝ +ℝ fcₙ *ℝ real-ℚ⁺ (inv-ℚ⁺ ε))
          ( chain-of-inequalities
            one-ℝ
            ≤ one-half-ℝ +ℝ one-half-ℝ
              by leq-eq-ℝ (inv twice-one-half-ℝ)
            ≤ one-half-ℝ +ℝ real-ℚ⁺ (one-half-ℚ⁺ *ℚ⁺ ε *ℚ⁺ inv-ℚ⁺ ε)
              by
                leq-eq-ℝ
                  ( ap-add-ℝ
                    ( refl)
                    ( ap
                      ( real-ℚ)
                      ( inv
                        ( is-retraction-right-div-ℚ⁺
                          ( ε)
                          ( one-half-ℚ)))))
            ≤ ( one-half-ℝ) +ℝ
              ( real-ℚ⁺ ε' *ℝ real-ℚ⁺ (inv-ℚ⁺ ε))
              by leq-eq-ℝ (ap-add-ℝ refl (inv (mul-real-ℚ _ _)))
            ≤ one-half-ℝ +ℝ fcₙ *ℝ real-ℚ⁺ (inv-ℚ⁺ ε)
              by
                preserves-leq-left-add-ℝ _ _ _
                  ( preserves-leq-right-mul-ℝ⁰⁺
                    ( nonnegative-real-ℚ⁺ (inv-ℚ⁺ ε))
                    ( ε/2≤fcₙ)))

    eq-succ-lower-bound-seq-leq-half-ε-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( real-ℚ⁺ (one-half-ℚ⁺ *ℚ⁺ ε))
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( seq-intermediate-value-theorem-ℝ n)) →
      lower-bound-seq-intermediate-value-theorem-ℝ (succ-ℕ n) ＝
      lower-bound-seq-intermediate-value-theorem-ℝ n
    eq-succ-lower-bound-seq-leq-half-ε-seq-intermediate-value-theorem-ℝ
      n ε/2≤fcₙ =
      eq-sim-ℝ
        ( similarity-reasoning-ℝ
          lower-bound-seq-intermediate-value-theorem-ℝ (succ-ℕ n)
          ~ℝ
            ( seq-intermediate-value-theorem-ℝ n) -ℝ
            ( one-ℝ *ℝ real-ℝ⁰⁺ (⟨b-a⟩/2^1+ n))
            by
              preserves-sim-diff-ℝ
                ( refl-sim-ℝ _)
                ( preserves-sim-right-mul-ℝ _ _ _
                  ( sim-one-interpolation-seq-leq-half-ε-seq-intermediate-value-theorem-ℝ
                    ( n)
                    ( ε/2≤fcₙ)))
          ~ℝ
            ( ( lower-bound-seq-intermediate-value-theorem-ℝ n) +ℝ
              ( ( seq-intermediate-value-theorem-ℝ n) -ℝ
                ( lower-bound-seq-intermediate-value-theorem-ℝ n))) -ℝ
            ( real-ℝ⁰⁺ (⟨b-a⟩/2^1+ n))
            by
              preserves-sim-diff-ℝ
                ( symmetric-sim-ℝ (add-right-diff-ℝ _ _))
                ( sim-eq-ℝ (left-unit-law-mul-ℝ _))
          ~ℝ
            ( ( lower-bound-seq-intermediate-value-theorem-ℝ n) +ℝ
              ( real-ℝ⁰⁺ (⟨b-a⟩/2^1+ n))) -ℝ
            ( real-ℝ⁰⁺ (⟨b-a⟩/2^1+ n))
            by
              sim-eq-ℝ
                ( ap-diff-ℝ
                  ( ap-add-ℝ
                    ( refl)
                    ( diff-lower-bound-seq-intermediate-value-theorem-ℝ n))
                  ( refl))
          ~ℝ lower-bound-seq-intermediate-value-theorem-ℝ n
            by cancel-right-add-diff-ℝ _ _)

    succ-upper-bound-seq-leq-half-ε-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( real-ℚ⁺ (one-half-ℚ⁺ *ℚ⁺ ε))
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( seq-intermediate-value-theorem-ℝ n)) →
      upper-bound-seq-intermediate-value-theorem-ℝ (succ-ℕ n) ＝
      seq-intermediate-value-theorem-ℝ n
    succ-upper-bound-seq-leq-half-ε-seq-intermediate-value-theorem-ℝ n ε/2≤fcₙ =
      equational-reasoning
      ( upper-bound-seq-intermediate-value-theorem-ℝ n) -ℝ
      ( real-ℝ⁰⁺ (shift-seq-intermediate-value-theorem-ℝ n))
      ＝
        ( ( seq-intermediate-value-theorem-ℝ n) +ℝ
          ( ( upper-bound-seq-intermediate-value-theorem-ℝ n) -ℝ
            ( seq-intermediate-value-theorem-ℝ n))) -ℝ
        ( one-ℝ *ℝ real-ℝ⁰⁺ (⟨b-a⟩/2^1+ n))
        by
          ap-diff-ℝ
            ( inv (eq-sim-ℝ (add-right-diff-ℝ _ _)))
            ( eq-sim-ℝ
              ( preserves-sim-right-mul-ℝ _ _ _
                ( sim-one-interpolation-seq-leq-half-ε-seq-intermediate-value-theorem-ℝ
                  ( n)
                  ( ε/2≤fcₙ))))
      ＝
        ( ( seq-intermediate-value-theorem-ℝ n) +ℝ
          ( real-ℝ⁰⁺ (⟨b-a⟩/2^1+ n))) -ℝ
        ( real-ℝ⁰⁺ (⟨b-a⟩/2^1+ n))
        by
          ap-diff-ℝ
            ( ap-add-ℝ
              ( refl)
              ( diff-upper-bound-seq-intermediate-value-theorem-ℝ n))
            ( left-unit-law-mul-ℝ _)
      ＝ seq-intermediate-value-theorem-ℝ n
        by eq-sim-ℝ (cancel-right-add-diff-ℝ _ _)
```

### If `ε/2 ≤ f cₙ`, then `aₙ₊₁ = aₙ` and `bₙ₊₁ = cₙ`

```agda
  abstract
    sim-zero-interpolation-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( seq-intermediate-value-theorem-ℝ n))
          ( neg-ℝ (real-ℚ⁺ (one-half-ℚ⁺ *ℚ⁺ ε))) →
      sim-ℝ
        ( pr1 (interpolation-seq-intermediate-value-theorem-ℝ n))
        ( zero-ℝ)
    sim-zero-interpolation-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ
      n fcₙ≤-ε/2 =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        ε' = one-half-ℚ⁺ *ℚ⁺ ε
        fcₙ =
          map-pointwise-continuous-map-ℝ
            ( f)
            ( seq-intermediate-value-theorem-ℝ n)
      in
        clamp-leq-lower-bound-closed-interval-ℝ
          ( unit-closed-interval-ℝ)
          ( one-half-ℝ +ℝ fcₙ *ℝ real-ℚ⁺ (inv-ℚ⁺ ε))
          ( chain-of-inequalities
            one-half-ℝ +ℝ fcₙ *ℝ real-ℚ⁺ (inv-ℚ⁺ ε)
            ≤ one-half-ℝ +ℝ (neg-ℝ (real-ℚ⁺ ε') *ℝ real-ℚ⁺ (inv-ℚ⁺ ε))
              by
                preserves-leq-left-add-ℝ _ _ _
                  ( preserves-leq-right-mul-ℝ⁰⁺
                    ( nonnegative-real-ℚ⁺ (inv-ℚ⁺ ε))
                    ( fcₙ≤-ε/2))
            ≤ one-half-ℝ -ℝ (real-ℚ⁺ ε' *ℝ real-ℚ⁺ (inv-ℚ⁺ ε))
              by leq-eq-ℝ (ap-add-ℝ refl (left-negative-law-mul-ℝ _ _))
            ≤ one-half-ℝ -ℝ real-ℚ⁺ (ε' *ℚ⁺ inv-ℚ⁺ ε)
              by leq-eq-ℝ (ap-diff-ℝ refl (mul-real-ℚ _ _))
            ≤ one-half-ℝ -ℝ one-half-ℝ
              by
                leq-eq-ℝ
                  ( ap-diff-ℝ
                    ( refl)
                    ( ap real-ℚ (is-retraction-right-div-ℚ⁺ ε one-half-ℚ)))
            ≤ zero-ℝ
              by leq-sim-ℝ (right-inverse-law-add-ℝ one-half-ℝ))

  abstract
    is-zero-shift-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( seq-intermediate-value-theorem-ℝ n))
          ( neg-ℝ (real-ℚ⁺ (one-half-ℚ⁺ *ℚ⁺ ε))) →
      sim-ℝ⁰⁺ (shift-seq-intermediate-value-theorem-ℝ n) zero-ℝ⁰⁺
    is-zero-shift-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ
      n fcₙ≤-ε/2 =
      similarity-reasoning-ℝ
        real-ℝ⁰⁺ (shift-seq-intermediate-value-theorem-ℝ n)
        ~ℝ zero-ℝ *ℝ _
          by
            preserves-sim-right-mul-ℝ _ _ _
              ( sim-zero-interpolation-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ
                ( n)
                ( fcₙ≤-ε/2))
        ~ℝ zero-ℝ
          by left-zero-law-mul-ℝ _

  abstract
    eq-succ-upper-bound-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( seq-intermediate-value-theorem-ℝ n))
          ( neg-ℝ (real-ℚ⁺ (one-half-ℚ⁺ *ℚ⁺ ε))) →
      upper-bound-seq-intermediate-value-theorem-ℝ (succ-ℕ n) ＝
      upper-bound-seq-intermediate-value-theorem-ℝ n
    eq-succ-upper-bound-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ
      n fcₙ≤-ε/2 =
      eq-sim-ℝ
        ( similarity-reasoning-ℝ
          ( upper-bound-seq-intermediate-value-theorem-ℝ n) -ℝ
          ( real-ℝ⁰⁺ (shift-seq-intermediate-value-theorem-ℝ n))
          ~ℝ upper-bound-seq-intermediate-value-theorem-ℝ n -ℝ zero-ℝ
            by
              preserves-sim-diff-ℝ
                ( refl-sim-ℝ _)
                ( is-zero-shift-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ
                  ( n)
                  ( fcₙ≤-ε/2))
          ~ℝ upper-bound-seq-intermediate-value-theorem-ℝ n
            by sim-eq-ℝ (right-unit-law-diff-ℝ _))

    succ-lower-bound-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( seq-intermediate-value-theorem-ℝ n))
          ( neg-ℝ (real-ℚ⁺ (one-half-ℚ⁺ *ℚ⁺ ε))) →
      lower-bound-seq-intermediate-value-theorem-ℝ (succ-ℕ n) ＝
      seq-intermediate-value-theorem-ℝ n
    succ-lower-bound-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ
      n fcₙ≤-ε/2 =
      eq-sim-ℝ
        ( similarity-reasoning-ℝ
          ( seq-intermediate-value-theorem-ℝ n) -ℝ
          ( real-ℝ⁰⁺ (shift-seq-intermediate-value-theorem-ℝ n))
          ~ℝ seq-intermediate-value-theorem-ℝ n -ℝ zero-ℝ
            by
              preserves-sim-diff-ℝ
                ( refl-sim-ℝ _)
                ( is-zero-shift-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ
                  ( n)
                  ( fcₙ≤-ε/2))
          ~ℝ seq-intermediate-value-theorem-ℝ n
            by sim-eq-ℝ (right-unit-law-diff-ℝ _))
```

### The key lemma

For all `m`, there [exists](foundation.existential-quantification.md) `n`
[less than or equal to](elementary-number-theory.inequality-natural-numbers.md)
`m` with `|f(cₙ)| ≤ ε` [or](foundation.disjunction.md) `f(aₙ) < 0 < f(bₙ)`.

```agda
  lemma-prop-intermediate-value-theorem-ℝ : (m : ℕ) → Prop l
  lemma-prop-intermediate-value-theorem-ℝ m =
    ( ∃
      ( ℕ)
      ( λ n →
        ( leq-ℕ-Prop n m) ∧
        ( leq-prop-ℝ
          ( abs-ℝ
            ( map-pointwise-continuous-map-ℝ
              ( f)
              ( seq-intermediate-value-theorem-ℝ n)))
          ( real-ℚ⁺ ε)))) ∨
    ( ( is-negative-prop-ℝ
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( lower-bound-seq-intermediate-value-theorem-ℝ m))) ∧
      ( is-positive-prop-ℝ
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( upper-bound-seq-intermediate-value-theorem-ℝ m))))

  abstract
    lemma-intermediate-value-theorem-ℝ :
      (m : ℕ) → type-Prop (lemma-prop-intermediate-value-theorem-ℝ m)
    lemma-intermediate-value-theorem-ℝ 0 = inr-disjunction (fa<0 , 0<fb)
    lemma-intermediate-value-theorem-ℝ (succ-ℕ m) =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        motive = lemma-prop-intermediate-value-theorem-ℝ (succ-ℕ m)
        ε' = one-half-ℚ⁺ *ℚ⁺ ε
        ε'<ε = le-left-mul-less-than-one-ℚ⁺ one-half-ℚ⁺ le-one-half-one-ℚ ε
        fcₘ =
          map-pointwise-continuous-map-ℝ
            ( f)
            ( seq-intermediate-value-theorem-ℝ m)
      in
        elim-disjunction
          ( motive)
          ( ( inl-disjunction) ∘
            ( map-tot-exists
              ( λ n →
                map-product
                  ( transitive-leq-ℕ n m (succ-ℕ m) (succ-leq-ℕ m)) id)))
          ( λ (faₘ<0 , 0<fbₘ) →
            elim-disjunction
              ( motive)
              ( λ -ε<fcₘ →
                elim-disjunction
                  ( motive)
                  ( λ ε'<fcₘ →
                    inr-disjunction
                      ( inv-tr
                          ( ( is-negative-ℝ) ∘
                            ( map-pointwise-continuous-map-ℝ f))
                          ( eq-succ-lower-bound-seq-leq-half-ε-seq-intermediate-value-theorem-ℝ
                            ( m)
                            ( leq-le-ℝ ε'<fcₘ))
                          ( faₘ<0) ,
                        inv-tr
                          ( ( is-positive-ℝ) ∘
                            ( map-pointwise-continuous-map-ℝ f))
                          ( succ-upper-bound-seq-leq-half-ε-seq-intermediate-value-theorem-ℝ
                            ( m)
                            ( leq-le-ℝ ε'<fcₘ))
                          ( is-positive-le-ℝ⁺
                            ( positive-real-ℚ⁺ ε')
                            ( _)
                            ( ε'<fcₘ))))
                  ( λ fcₘ<ε →
                    inl-disjunction
                      ( intro-exists
                        ( m)
                        ( succ-leq-ℕ m ,
                          leq-abs-leq-leq-neg-ℝ'
                            ( leq-le-ℝ fcₘ<ε)
                            ( leq-le-ℝ -ε<fcₘ))))
                  ( cotransitive-le-ℝ
                    ( real-ℚ⁺ ε')
                    ( real-ℚ⁺ ε)
                    ( fcₘ)
                    ( preserves-le-real-ℚ ε'<ε)))
              ( λ fcₘ<-ε' →
                inr-disjunction
                  ( inv-tr
                      ( ( is-negative-ℝ) ∘
                        ( map-pointwise-continuous-map-ℝ f))
                      ( succ-lower-bound-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ
                        ( m)
                        ( leq-le-ℝ fcₘ<-ε'))
                      ( is-negative-le-real-ℝ⁻
                        ( fcₘ)
                        ( neg-ℝ⁺ (positive-real-ℚ⁺ ε'))
                        ( fcₘ<-ε')) ,
                    inv-tr
                      ( ( is-positive-ℝ) ∘
                        ( map-pointwise-continuous-map-ℝ f))
                      ( eq-succ-upper-bound-seq-leq-neg-half-ε-seq-intermediate-value-theorem-ℝ
                        ( m)
                        ( leq-le-ℝ fcₘ<-ε'))
                      ( 0<fbₘ)))
              ( cotransitive-le-ℝ
                ( neg-ℝ (real-ℚ⁺ ε))
                ( neg-ℝ (real-ℚ⁺ ε'))
                ( fcₘ)
                ( neg-le-ℝ (preserves-le-real-ℚ ε'<ε))))
          ( lemma-intermediate-value-theorem-ℝ m)
```

### The intermediate value theorem follows from the lemma

```agda
  abstract
    intermediate-value-theorem-ℝ :
      exists
        ( type-closed-interval-ℝ l ((a , b) , a≤b))
        ( λ (c , _) →
          leq-prop-ℝ
            ( abs-ℝ (map-pointwise-continuous-map-ℝ f c))
            ( real-ℚ⁺ ε))
    intermediate-value-theorem-ℝ =
      let
        motive =
          ∃ ( type-closed-interval-ℝ l ((a , b) , a≤b))
            ( λ (c , _) →
              leq-prop-ℝ
                ( abs-ℝ (map-pointwise-continuous-map-ℝ f c))
                ( real-ℚ⁺ ε))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open do-syntax-trunc-Prop motive
      in do
        (μf , is-mod-μf) ←
          is-pointwise-continuous-map-pointwise-continuous-map-ℝ
            ( f)
            ( lim-seq-intermediate-value-theorem-ℝ)
        let (δ₁ , δ₂ , δ₁+δ₂=δ) = split-ℚ⁺ (μf ε)
        (μseq , is-mod-μseq) ←
          is-limit-lim-seq-intermediate-value-theorem-ℝ
        (μba , is-mod-μba) ← is-zero-limit-⟨b-a⟩/2^1+
        let
          m = max-ℕ (μseq δ₁) (μba δ₂)
          ⟨b-a⟩/2¹⁺ᵐ≤δ₂ =
            chain-of-inequalities
              real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m)
              ≤ real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m) -ℝ zero-ℝ
                by leq-eq-ℝ (inv (right-unit-law-diff-ℝ _))
              ≤ dist-ℝ (real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m)) zero-ℝ
                by leq-abs-ℝ _
              ≤ dist-ℝ (real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m)) (raise-zero-ℝ l)
                by
                  leq-sim-ℝ
                    ( preserves-dist-right-sim-ℝ (sim-raise-ℝ l zero-ℝ))
              ≤ real-ℚ⁺ δ₂
                by
                  leq-dist-neighborhood-ℝ
                    ( δ₂)
                    ( real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m))
                    ( raise-zero-ℝ l)
                    ( is-mod-μba
                      ( δ₂)
                      ( m)
                      ( right-leq-max-ℕ (μseq δ₁) (μba δ₂)))
          Nδ₂cₘbₘ :
            neighborhood-ℝ
              ( l)
              ( δ₂)
              ( seq-intermediate-value-theorem-ℝ m)
              ( upper-bound-seq-intermediate-value-theorem-ℝ m)
          Nδ₂cₘbₘ =
            neighborhood-dist-ℝ
              ( δ₂)
              ( seq-intermediate-value-theorem-ℝ m)
              ( upper-bound-seq-intermediate-value-theorem-ℝ m)
              ( chain-of-inequalities
                dist-ℝ
                  ( seq-intermediate-value-theorem-ℝ m)
                  ( upper-bound-seq-intermediate-value-theorem-ℝ m)
                ≤ dist-ℝ
                    ( upper-bound-seq-intermediate-value-theorem-ℝ m)
                    ( seq-intermediate-value-theorem-ℝ m)
                  by leq-eq-ℝ (commutative-dist-ℝ _ _)
                ≤ abs-ℝ (real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m))
                  by
                    leq-eq-ℝ
                      ( ap
                        ( abs-ℝ)
                        ( diff-upper-bound-seq-intermediate-value-theorem-ℝ m))
                ≤ real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m)
                  by leq-eq-ℝ (abs-real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m))
                ≤ real-ℚ⁺ δ₂
                  by ⟨b-a⟩/2¹⁺ᵐ≤δ₂)
          Nδ₂cₘaₘ :
            neighborhood-ℝ
              ( l)
              ( δ₂)
              ( seq-intermediate-value-theorem-ℝ m)
              ( lower-bound-seq-intermediate-value-theorem-ℝ m)
          Nδ₂cₘaₘ =
            neighborhood-dist-ℝ
              ( δ₂)
              ( seq-intermediate-value-theorem-ℝ m)
              ( lower-bound-seq-intermediate-value-theorem-ℝ m)
              ( chain-of-inequalities
                dist-ℝ
                  ( seq-intermediate-value-theorem-ℝ m)
                  ( lower-bound-seq-intermediate-value-theorem-ℝ m)
                ≤ abs-ℝ (real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m))
                  by
                    leq-eq-ℝ
                      ( ap
                        ( abs-ℝ)
                        ( diff-lower-bound-seq-intermediate-value-theorem-ℝ m))
                ≤ real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m)
                  by leq-eq-ℝ (abs-real-ℝ⁰⁺ (⟨b-a⟩/2^1+ m))
                ≤ real-ℚ⁺ δ₂
                  by ⟨b-a⟩/2¹⁺ᵐ≤δ₂)
          Nδ₁ccₘ :
            neighborhood-ℝ l
              ( δ₁)
              ( lim-seq-intermediate-value-theorem-ℝ)
              ( seq-intermediate-value-theorem-ℝ m)
          Nδ₁ccₘ =
            is-symmetric-neighborhood-ℝ
              ( δ₁)
              ( seq-intermediate-value-theorem-ℝ m)
              ( lim-seq-intermediate-value-theorem-ℝ)
              ( is-mod-μseq
                ( δ₁)
                ( m)
                ( left-leq-max-ℕ (μseq δ₁) (μba δ₂)))
          Nμfεcbₘ :
            neighborhood-ℝ
              ( l)
              ( μf ε)
              ( lim-seq-intermediate-value-theorem-ℝ)
              ( upper-bound-seq-intermediate-value-theorem-ℝ m)
          Nμfεcbₘ =
            tr
              ( λ θ →
                neighborhood-ℝ l
                  ( θ)
                  ( lim-seq-intermediate-value-theorem-ℝ)
                  ( upper-bound-seq-intermediate-value-theorem-ℝ m))
              ( δ₁+δ₂=δ)
              ( is-triangular-neighborhood-ℝ
                ( lim-seq-intermediate-value-theorem-ℝ)
                ( seq-intermediate-value-theorem-ℝ m)
                ( upper-bound-seq-intermediate-value-theorem-ℝ m)
                ( δ₁)
                ( δ₂)
                ( Nδ₂cₘbₘ)
                ( Nδ₁ccₘ))
          Nμfεcaₘ :
            neighborhood-ℝ
              ( l)
              ( μf ε)
              ( lim-seq-intermediate-value-theorem-ℝ)
              ( lower-bound-seq-intermediate-value-theorem-ℝ m)
          Nμfεcaₘ =
            tr
              ( λ θ →
                neighborhood-ℝ l
                  ( θ)
                  ( lim-seq-intermediate-value-theorem-ℝ)
                  ( lower-bound-seq-intermediate-value-theorem-ℝ m))
              ( δ₁+δ₂=δ)
              ( is-triangular-neighborhood-ℝ
                ( lim-seq-intermediate-value-theorem-ℝ)
                ( seq-intermediate-value-theorem-ℝ m)
                ( lower-bound-seq-intermediate-value-theorem-ℝ m)
                ( δ₁)
                ( δ₂)
                ( Nδ₂cₘaₘ)
                ( Nδ₁ccₘ))
        elim-disjunction
          ( motive)
          ( λ ∃n:|cₙ|≤ε → do
            (n , n≤m , |cₙ|≤ε) ← ∃n:|cₙ|≤ε
            intro-exists
              ( seq-intermediate-value-theorem-ℝ n ,
                lower-bound-of-seq-intermediate-value-theorem-ℝ n ,
                upper-bound-of-seq-intermediate-value-theorem-ℝ n)
              ( |cₙ|≤ε))
          ( λ (faₘ<0 , 0<fbₘ) →
            intro-exists
              ( lim-seq-intermediate-value-theorem-ℝ ,
                lower-bound-lim-seq-intermediate-value-theorem-ℝ ,
                upper-bound-lim-seq-intermediate-value-theorem-ℝ)
              ( leq-abs-leq-leq-neg-ℝ'
                ( chain-of-inequalities
                  map-pointwise-continuous-map-ℝ
                    ( f)
                    ( lim-seq-intermediate-value-theorem-ℝ)
                  ≤ ( map-pointwise-continuous-map-ℝ
                      ( f)
                      ( lower-bound-seq-intermediate-value-theorem-ℝ m)) +ℝ
                    ( real-ℚ⁺ ε)
                    by
                      left-leq-real-bound-neighborhood-ℝ
                        ( ε)
                        ( map-pointwise-continuous-map-ℝ
                          ( f)
                          ( lim-seq-intermediate-value-theorem-ℝ))
                        ( map-pointwise-continuous-map-ℝ
                          ( f)
                          ( lower-bound-seq-intermediate-value-theorem-ℝ m))
                        ( is-mod-μf
                          ( ε)
                          ( lower-bound-seq-intermediate-value-theorem-ℝ m)
                          ( Nμfεcaₘ))
                  ≤ zero-ℝ +ℝ real-ℚ⁺ ε
                    by preserves-leq-right-add-ℝ _ _ _ (leq-le-ℝ faₘ<0)
                  ≤ real-ℚ⁺ ε
                    by leq-eq-ℝ (left-unit-law-add-ℝ _))
                ( chain-of-inequalities
                  neg-ℝ (real-ℚ⁺ ε)
                  ≤ zero-ℝ -ℝ real-ℚ⁺ ε
                    by leq-eq-ℝ (inv (left-unit-law-add-ℝ _))
                  ≤ ( map-pointwise-continuous-map-ℝ
                      ( f)
                      ( upper-bound-seq-intermediate-value-theorem-ℝ m)) -ℝ
                    ( real-ℚ⁺ ε)
                    by preserves-leq-right-add-ℝ _ _ _ (leq-le-ℝ 0<fbₘ)
                  ≤ map-pointwise-continuous-map-ℝ
                      ( f)
                      ( lim-seq-intermediate-value-theorem-ℝ)
                    by
                      leq-transpose-right-add-ℝ _ _ _
                        ( right-leq-real-bound-neighborhood-ℝ
                          ( ε)
                          ( map-pointwise-continuous-map-ℝ
                            ( f)
                            ( lim-seq-intermediate-value-theorem-ℝ))
                          ( map-pointwise-continuous-map-ℝ
                            ( f)
                            ( upper-bound-seq-intermediate-value-theorem-ℝ m))
                          ( is-mod-μf
                            ( ε)
                            ( upper-bound-seq-intermediate-value-theorem-ℝ m)
                            ( Nμfεcbₘ))))))
          ( lemma-intermediate-value-theorem-ℝ m)
```

## External links

- [Intermediate value theorem](https://ncatlab.org/nlab/show/intermediate+value+theorem)
  on $n$Lab
- [Intermediate value theorem](https://en.wikipedia.org/wiki/Intermediate_value_theorem)
  on Wikipedia

## References

{{#bibliography}}
