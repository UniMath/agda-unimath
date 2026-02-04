# The intermediate value theorem

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.intermediate-value-theorem where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.homotopies
open import foundation.identity-types
open import foundation.law-of-excluded-middle
open import foundation.propositional-truncations
open import foundation.universe-levels

open import lists.sequences
open import lists.subsequences

open import order-theory.large-posets

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.binary-mean-real-numbers
open import real-numbers.cauchy-sequences-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.decreasing-sequences-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.increasing-sequences-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.iterated-halving-difference-real-numbers
open import real-numbers.limits-of-sequences-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonpositive-real-numbers
open import real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-sequences-approximating-zero
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

The
{{#concept "intermediate value theorem" WDID=Q245098 WD="intermediate value theorem"}}
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
[constructive intermediate value theorem](analysis.constructive-intermediate-value-theorem.md),
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
    lower-bound-sequence-intermediate-value-theorem-ℝ :
      sequence (ℝ l1)
    upper-bound-sequence-intermediate-value-theorem-ℝ :
      sequence (ℝ l1)
    sequence-intermediate-value-theorem-ℝ : sequence (ℝ l1)

    sign-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      ( is-nonpositive-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( sequence-intermediate-value-theorem-ℝ n))) +
      ( is-nonnegative-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( sequence-intermediate-value-theorem-ℝ n)))

    sequence-intermediate-value-theorem-ℝ n =
      binary-mean-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)

    sign-sequence-intermediate-value-theorem-ℝ n =
      linear-leq-lem-ℝ
        ( lem)
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( sequence-intermediate-value-theorem-ℝ n))
        ( zero-ℝ)

    lower-bound-sequence-intermediate-value-theorem-ℝ 0 = a
    lower-bound-sequence-intermediate-value-theorem-ℝ (succ-ℕ n) =
      rec-coproduct
        ( λ _ → sequence-intermediate-value-theorem-ℝ n)
        ( λ _ → lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( sign-sequence-intermediate-value-theorem-ℝ n)

    upper-bound-sequence-intermediate-value-theorem-ℝ 0 = b
    upper-bound-sequence-intermediate-value-theorem-ℝ (succ-ℕ n) =
      rec-coproduct
        ( λ _ → upper-bound-sequence-intermediate-value-theorem-ℝ n)
        ( λ _ → sequence-intermediate-value-theorem-ℝ n)
        ( sign-sequence-intermediate-value-theorem-ℝ n)
```

### `aₙ ≤ cₙ ≤ bₙ`

```agda
  abstract interleaved mutual
    leq-lower-upper-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)

    leq-lower-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( sequence-intermediate-value-theorem-ℝ n)

    leq-upper-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( sequence-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)

    leq-lower-upper-bound-sequence-intermediate-value-theorem-ℝ 0 =
      a≤b
    leq-lower-upper-bound-sequence-intermediate-value-theorem-ℝ
      (succ-ℕ n)
      with sign-sequence-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 =
      leq-upper-bound-sequence-intermediate-value-theorem-ℝ n
    ... | inr 0≤fcₙ =
      leq-lower-bound-sequence-intermediate-value-theorem-ℝ n

    leq-lower-bound-sequence-intermediate-value-theorem-ℝ n =
      leq-binary-mean-leq-both-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( refl-leq-ℝ _)
        ( leq-lower-upper-bound-sequence-intermediate-value-theorem-ℝ
          ( n))

    leq-upper-bound-sequence-intermediate-value-theorem-ℝ n =
      geq-binary-mean-geq-both-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)
        ( leq-lower-upper-bound-sequence-intermediate-value-theorem-ℝ
          ( n))
        ( refl-leq-ℝ _)
```

### `f aₙ ≤ 0`

```agda
  abstract
    is-nonpositive-map-lower-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      is-nonpositive-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( lower-bound-sequence-intermediate-value-theorem-ℝ n))
    is-nonpositive-map-lower-bound-sequence-intermediate-value-theorem-ℝ
      0 =
      fa≤0
    is-nonpositive-map-lower-bound-sequence-intermediate-value-theorem-ℝ
      (succ-ℕ n)
      with sign-sequence-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 = fcₙ≤0
    ... | inr 0≤fcₙ =
      is-nonpositive-map-lower-bound-sequence-intermediate-value-theorem-ℝ
        ( n)
```

### `0 ≤ f bₙ`

```agda
  abstract
    is-nonnegative-map-upper-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      is-nonnegative-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( upper-bound-sequence-intermediate-value-theorem-ℝ n))
    is-nonnegative-map-upper-bound-sequence-intermediate-value-theorem-ℝ
      0 =
      0≤fb
    is-nonnegative-map-upper-bound-sequence-intermediate-value-theorem-ℝ
      (succ-ℕ n) with sign-sequence-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 =
      is-nonnegative-map-upper-bound-sequence-intermediate-value-theorem-ℝ
        ( n)
    ... | inr 0≤fcₙ = 0≤fcₙ
```

### `bₙ - aₙ = (b-a)/2ⁿ`

```agda
  abstract interleaved mutual
    diff-upper-lower-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      ( ( upper-bound-sequence-intermediate-value-theorem-ℝ n) -ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)) ＝
      iterated-half-diff-leq-ℝ a≤b n

    diff-upper-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      ( ( upper-bound-sequence-intermediate-value-theorem-ℝ n) -ℝ
        ( sequence-intermediate-value-theorem-ℝ n)) ＝
      iterated-half-diff-leq-ℝ a≤b (succ-ℕ n)

    diff-lower-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      ( ( sequence-intermediate-value-theorem-ℝ n) -ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)) ＝
      iterated-half-diff-leq-ℝ a≤b (succ-ℕ n)

    diff-upper-lower-bound-sequence-intermediate-value-theorem-ℝ 0 =
      inv (right-unit-law-mul-ℝ _)
    diff-upper-lower-bound-sequence-intermediate-value-theorem-ℝ
      (succ-ℕ n) with sign-sequence-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 =
      diff-upper-bound-sequence-intermediate-value-theorem-ℝ n
    ... | inr 0≤fcₙ =
      diff-lower-bound-sequence-intermediate-value-theorem-ℝ n

    diff-upper-bound-sequence-intermediate-value-theorem-ℝ n =
      equational-reasoning
        upper-bound-sequence-intermediate-value-theorem-ℝ n -ℝ
        sequence-intermediate-value-theorem-ℝ n
        ＝
          binary-mean-ℝ
            ( upper-bound-sequence-intermediate-value-theorem-ℝ n)
            ( neg-ℝ
              ( lower-bound-sequence-intermediate-value-theorem-ℝ n))
          by diff-right-binary-mean-ℝ _ _
        ＝ one-half-ℝ *ℝ iterated-half-diff-leq-ℝ a≤b n
          by
            ap-mul-ℝ
              ( refl {x = one-half-ℝ})
              ( diff-upper-lower-bound-sequence-intermediate-value-theorem-ℝ
                ( n))
        ＝ iterated-half-diff-leq-ℝ a≤b (succ-ℕ n)
          by mul-one-half-iterated-half-diff-leq-ℝ a≤b n

    diff-lower-bound-sequence-intermediate-value-theorem-ℝ n =
      equational-reasoning
        sequence-intermediate-value-theorem-ℝ n -ℝ
        lower-bound-sequence-intermediate-value-theorem-ℝ n
        ＝
          binary-mean-ℝ
            ( upper-bound-sequence-intermediate-value-theorem-ℝ n)
            ( neg-ℝ
              ( lower-bound-sequence-intermediate-value-theorem-ℝ n))
          by diff-left-binary-mean-ℝ _ _
        ＝ one-half-ℝ *ℝ iterated-half-diff-leq-ℝ a≤b n
          by
            ap-mul-ℝ
              ( refl {x = one-half-ℝ})
              ( diff-upper-lower-bound-sequence-intermediate-value-theorem-ℝ
                ( n))
        ＝ iterated-half-diff-leq-ℝ a≤b (succ-ℕ n)
          by mul-one-half-iterated-half-diff-leq-ℝ a≤b n
```

### The sequence `aₙ` is increasing

```agda
  abstract
    leq-succ-lower-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( lower-bound-sequence-intermediate-value-theorem-ℝ
          ( succ-ℕ n))
    leq-succ-lower-bound-sequence-intermediate-value-theorem-ℝ n
      with sign-sequence-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 =
      leq-lower-bound-sequence-intermediate-value-theorem-ℝ n
    ... | inr 0≤fcₙ = refl-leq-ℝ _

    is-increasing-lower-bound-sequence-intermediate-value-theorem-ℝ :
      is-increasing-sequence-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ)
    is-increasing-lower-bound-sequence-intermediate-value-theorem-ℝ =
      is-increasing-leq-succ-sequence-ℝ _
        ( leq-succ-lower-bound-sequence-intermediate-value-theorem-ℝ)
```

### The sequence `bₙ` is decreasing

```agda
  abstract
    leq-succ-upper-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( upper-bound-sequence-intermediate-value-theorem-ℝ
          ( succ-ℕ n))
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)
    leq-succ-upper-bound-sequence-intermediate-value-theorem-ℝ n
      with sign-sequence-intermediate-value-theorem-ℝ n
    ... | inl fcₙ≤0 = refl-leq-ℝ _
    ... | inr 0≤fcₙ =
      leq-upper-bound-sequence-intermediate-value-theorem-ℝ n

    is-decreasing-upper-bound-sequence-intermediate-value-theorem-ℝ :
      is-decreasing-sequence-ℝ
        ( upper-bound-sequence-intermediate-value-theorem-ℝ)
    is-decreasing-upper-bound-sequence-intermediate-value-theorem-ℝ =
      is-decreasing-leq-succ-sequence-ℝ _
        ( leq-succ-upper-bound-sequence-intermediate-value-theorem-ℝ)
```

### The sequence `cₙ` is Cauchy

```agda
  abstract
    is-cauchy-sequence-intermediate-value-theorem-ℝ :
      is-cauchy-sequence-ℝ sequence-intermediate-value-theorem-ℝ
    is-cauchy-sequence-intermediate-value-theorem-ℝ =
      is-cauchy-squeeze-theorem-sequence-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ)
        ( sequence-intermediate-value-theorem-ℝ)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ)
        ( leq-lower-bound-sequence-intermediate-value-theorem-ℝ)
        ( leq-upper-bound-sequence-intermediate-value-theorem-ℝ)
        ( is-increasing-lower-bound-sequence-intermediate-value-theorem-ℝ)
        ( is-decreasing-upper-bound-sequence-intermediate-value-theorem-ℝ)
        ( preserves-is-zero-limit-htpy-sequence-ℝ
          ( inv-htpy
            ( diff-upper-lower-bound-sequence-intermediate-value-theorem-ℝ))
          ( is-zero-limit-iterated-half-diff-leq-ℝ a≤b))

    has-limit-sequence-intermediate-value-theorem-ℝ :
      has-limit-sequence-ℝ sequence-intermediate-value-theorem-ℝ
    has-limit-sequence-intermediate-value-theorem-ℝ =
      has-limit-cauchy-sequence-ℝ
        ( sequence-intermediate-value-theorem-ℝ ,
          is-cauchy-sequence-intermediate-value-theorem-ℝ)

  limit-sequence-intermediate-value-theorem-ℝ : ℝ l1
  limit-sequence-intermediate-value-theorem-ℝ =
    pr1 has-limit-sequence-intermediate-value-theorem-ℝ

  is-limit-sequence-intermediate-value-theorem-ℝ :
    is-limit-sequence-ℝ
      ( sequence-intermediate-value-theorem-ℝ)
      ( limit-sequence-intermediate-value-theorem-ℝ)
  is-limit-sequence-intermediate-value-theorem-ℝ =
    pr2 has-limit-sequence-intermediate-value-theorem-ℝ
```

### `a ≤ c ≤ b`

```agda
  abstract
    leq-lower-bound-lim-sequence-intermediate-value-theorem-ℝ :
      leq-ℝ a limit-sequence-intermediate-value-theorem-ℝ
    leq-lower-bound-lim-sequence-intermediate-value-theorem-ℝ =
      lower-bound-lim-lower-bound-sequence-ℝ
        ( a)
        ( λ n →
          transitive-leq-ℝ _ _ _
            ( leq-lower-bound-sequence-intermediate-value-theorem-ℝ n)
            ( is-increasing-lower-bound-sequence-intermediate-value-theorem-ℝ
              ( 0)
              ( n)
              ( _)))
        ( is-limit-sequence-intermediate-value-theorem-ℝ)

    leq-upper-bound-lim-sequence-intermediate-value-theorem-ℝ :
      leq-ℝ limit-sequence-intermediate-value-theorem-ℝ b
    leq-upper-bound-lim-sequence-intermediate-value-theorem-ℝ =
      upper-bound-lim-upper-bound-sequence-ℝ
        ( b)
        ( λ n →
          transitive-leq-ℝ _ _ _
            ( is-decreasing-upper-bound-sequence-intermediate-value-theorem-ℝ
              ( 0)
              ( n)
              ( _))
            ( leq-upper-bound-sequence-intermediate-value-theorem-ℝ
              ( n)))
        ( is-limit-sequence-intermediate-value-theorem-ℝ)
```

### `f c` is nonpositive

```agda
  abstract
    is-nonpositive-map-limit-sequence-intermediate-value-theorem-ℝ :
      is-nonpositive-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( limit-sequence-intermediate-value-theorem-ℝ))
    is-nonpositive-map-limit-sequence-intermediate-value-theorem-ℝ =
      leq-not-le-ℝ _ _
        ( λ 0<fc →
          let
            open do-syntax-trunc-Prop empty-Prop
            open inequality-reasoning-Large-Poset ℝ-Large-Poset
          in do
            (ε , ε<fc) ← exists-ℚ⁺-in-lower-cut-ℝ⁺ (_ , 0<fc)
            (δ , Hδ) ←
              is-pointwise-ε-δ-continuous-map-pointwise-ε-δ-continuous-endomap-ℝ
                ( f)
                ( limit-sequence-intermediate-value-theorem-ℝ)
                ( ε)
            (δ' , 2δ'<δ) ← double-le-ℚ⁺ δ
            (μba , is-mod-μba) ←
              is-limit-subsequence-ℝ
                ( tail-subsequence (iterated-half-diff-leq-ℝ a≤b))
                ( is-zero-limit-iterated-half-diff-leq-ℝ a≤b)
            (μc , is-mod-μc) ←
              is-limit-sequence-intermediate-value-theorem-ℝ
            let
              Nba = μba δ'
              Nc = μc δ'
              N = max-ℕ Nba Nc
              cN = sequence-intermediate-value-theorem-ℝ N
              aN = lower-bound-sequence-intermediate-value-theorem-ℝ N
              Nδ'aNcN : neighborhood-ℝ l1 δ' aN cN
              Nδ'aNcN =
                neighborhood-real-bound-each-leq-ℝ _ _ _
                  ( transitive-leq-ℝ _ _ _
                    ( leq-left-add-real-ℚ⁺ _ _)
                    ( leq-lower-bound-sequence-intermediate-value-theorem-ℝ
                      ( N)))
                  ( chain-of-inequalities
                    cN
                    ≤ (cN -ℝ aN) +ℝ aN
                      by leq-sim-ℝ' (cancel-right-diff-add-ℝ _ _)
                    ≤ iterated-half-diff-leq-ℝ a≤b (succ-ℕ N) +ℝ aN
                      by
                        leq-eq-ℝ
                          ( ap-add-ℝ
                            ( diff-lower-bound-sequence-intermediate-value-theorem-ℝ
                              ( N))
                            ( refl))
                    ≤ (raise-zero-ℝ l1 +ℝ real-ℚ⁺ δ') +ℝ aN
                      by
                        preserves-leq-right-add-ℝ _ _ _
                          ( left-leq-real-bound-neighborhood-ℝ _ _ _
                            ( is-mod-μba δ' N (left-leq-max-ℕ Nba Nc)))
                    ≤ (raise-zero-ℝ l1 +ℝ aN) +ℝ real-ℚ⁺ δ'
                      by leq-eq-ℝ (right-swap-add-ℝ _ _ _)
                    ≤ aN +ℝ real-ℚ⁺ δ'
                      by
                        leq-eq-ℝ (ap-add-ℝ (left-raise-zero-law-add-ℝ aN) refl))
              NδaNc =
                monotonic-neighborhood-ℝ _ _
                  ( δ' +ℚ⁺ δ')
                  ( δ)
                  ( 2δ'<δ)
                  ( is-triangular-neighborhood-ℝ _ _ _ _ _
                    ( is-mod-μc δ' N (right-leq-max-ℕ Nba Nc))
                    ( Nδ'aNcN))
            not-leq-le-ℝ
              ( real-ℚ⁺ ε)
              ( map-pointwise-ε-δ-continuous-endomap-ℝ
                ( f)
                ( limit-sequence-intermediate-value-theorem-ℝ))
              ( le-real-is-in-lower-cut-ℝ _ ε<fc)
              ( chain-of-inequalities
                map-pointwise-ε-δ-continuous-endomap-ℝ
                  ( f)
                  ( limit-sequence-intermediate-value-theorem-ℝ)
                ≤ map-pointwise-ε-δ-continuous-endomap-ℝ f aN +ℝ real-ℚ⁺ ε
                  by
                    left-leq-real-bound-neighborhood-ℝ _ _ _
                      ( Hδ aN (is-symmetric-neighborhood-ℝ _ _ _ NδaNc))
                ≤ zero-ℝ +ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-right-add-ℝ _ _ _
                      ( is-nonpositive-map-lower-bound-sequence-intermediate-value-theorem-ℝ
                        ( N))
                ≤ real-ℚ⁺ ε
                  by leq-eq-ℝ (left-unit-law-add-ℝ _)))
```

### `f c` is nonnegative

```agda
  abstract
    is-nonnegative-map-limit-sequence-intermediate-value-theorem-ℝ :
      is-nonnegative-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ
          ( f)
          ( limit-sequence-intermediate-value-theorem-ℝ))
    is-nonnegative-map-limit-sequence-intermediate-value-theorem-ℝ =
      leq-not-le-ℝ _ _
        ( λ fc<0 →
          let
            open do-syntax-trunc-Prop empty-Prop
            open inequality-reasoning-Large-Poset ℝ-Large-Poset
          in do
            (ε , fc+ε<0) ← exists-positive-rational-separation-le-ℝ fc<0
            (δ , Hδ) ←
              is-pointwise-ε-δ-continuous-map-pointwise-ε-δ-continuous-endomap-ℝ
                ( f)
                ( limit-sequence-intermediate-value-theorem-ℝ)
                ( ε)
            (δ' , 2δ'<δ) ← double-le-ℚ⁺ δ
            (μba , is-mod-μba) ←
              is-limit-subsequence-ℝ
                ( tail-subsequence (iterated-half-diff-leq-ℝ a≤b))
                ( is-zero-limit-iterated-half-diff-leq-ℝ a≤b)
            (μc , is-mod-μc) ←
              is-limit-sequence-intermediate-value-theorem-ℝ
            let
              Nba = μba δ'
              Nc = μc δ'
              N = max-ℕ Nba Nc
              cN = sequence-intermediate-value-theorem-ℝ N
              bN = upper-bound-sequence-intermediate-value-theorem-ℝ N
              Nδ'bNcN : neighborhood-ℝ l1 δ' bN cN
              Nδ'bNcN =
                neighborhood-real-bound-each-leq-ℝ _ _ _
                  ( chain-of-inequalities
                    bN
                    ≤ (bN -ℝ cN) +ℝ cN
                      by leq-sim-ℝ' (cancel-right-diff-add-ℝ _ _)
                    ≤ iterated-half-diff-leq-ℝ a≤b (succ-ℕ N) +ℝ cN
                      by
                        leq-eq-ℝ
                          ( ap-add-ℝ
                            ( diff-upper-bound-sequence-intermediate-value-theorem-ℝ
                              ( N))
                            ( refl))
                    ≤ (raise-zero-ℝ l1 +ℝ real-ℚ⁺ δ') +ℝ cN
                      by
                        preserves-leq-right-add-ℝ _ _ _
                          ( left-leq-real-bound-neighborhood-ℝ _ _ _
                            ( is-mod-μba δ' N (left-leq-max-ℕ Nba Nc)))
                    ≤ (raise-zero-ℝ l1 +ℝ cN) +ℝ real-ℚ⁺ δ'
                      by leq-eq-ℝ (right-swap-add-ℝ _ _ _)
                    ≤ cN +ℝ real-ℚ⁺ δ'
                      by
                        leq-eq-ℝ (ap-add-ℝ (left-raise-zero-law-add-ℝ cN) refl))
                  ( transitive-leq-ℝ _ _ _
                    ( leq-left-add-real-ℚ⁺ _ _)
                    ( leq-upper-bound-sequence-intermediate-value-theorem-ℝ
                      ( N)))
              NδbNc =
                monotonic-neighborhood-ℝ _ _
                  ( δ' +ℚ⁺ δ')
                  ( δ)
                  ( 2δ'<δ)
                  ( is-triangular-neighborhood-ℝ _ _ _ _ _
                    ( is-mod-μc δ' N (right-leq-max-ℕ Nba Nc))
                    ( Nδ'bNcN))
            not-leq-le-ℝ _ _
              ( fc+ε<0)
              ( chain-of-inequalities
                zero-ℝ
                ≤ map-pointwise-ε-δ-continuous-endomap-ℝ
                    ( f)
                    ( bN)
                  by
                    is-nonnegative-map-upper-bound-sequence-intermediate-value-theorem-ℝ
                      ( N)
                ≤ ( map-pointwise-ε-δ-continuous-endomap-ℝ
                    ( f)
                    ( limit-sequence-intermediate-value-theorem-ℝ)) +ℝ
                  ( real-ℚ⁺ ε)
                  by
                    right-leq-real-bound-neighborhood-ℝ _ _ _
                      ( Hδ bN (is-symmetric-neighborhood-ℝ _ _ _ NδbNc))))

    intermediate-value-theorem-ℝ :
      exists
        ( type-closed-interval-ℝ l1 [a,b])
        ( λ (x , _ , _) →
          is-zero-prop-ℝ (map-pointwise-ε-δ-continuous-endomap-ℝ f x))
    intermediate-value-theorem-ℝ =
      intro-exists
        ( limit-sequence-intermediate-value-theorem-ℝ ,
          leq-lower-bound-lim-sequence-intermediate-value-theorem-ℝ ,
          leq-upper-bound-lim-sequence-intermediate-value-theorem-ℝ)
        ( sim-sim-leq-ℝ
          ( is-nonpositive-map-limit-sequence-intermediate-value-theorem-ℝ ,
            is-nonnegative-map-limit-sequence-intermediate-value-theorem-ℝ))
```

## External links

- [Intermediate value theorem](https://ncatlab.org/nlab/show/intermediate+value+theorem)
  on $n$Lab
- [Intermediate value theorem](https://en.wikipedia.org/wiki/Intermediate_value_theorem)
  on Wikipedia
