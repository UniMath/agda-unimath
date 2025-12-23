# The intermediate value theorem

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.intermediate-value-theorem where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-positive-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import lists.sequences

open import logic.functoriality-existential-quantification

open import order-theory.decreasing-sequences-posets
open import order-theory.increasing-sequences-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.binary-mean-real-numbers
open import real-numbers.cauchy-sequences-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.limits-sequences-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.pointwise-continuous-functions-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
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
    lower-bound-sequence-intermediate-value-theorem-ℝ : sequence (ℝ l)

    upper-bound-sequence-intermediate-value-theorem-ℝ : sequence (ℝ l)

    sequence-intermediate-value-theorem-ℝ : sequence (ℝ l)

    sequence-intermediate-value-theorem-ℝ n =
      binary-mean-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)

    interpolation-sequence-intermediate-value-theorem-ℝ :
      sequence (type-closed-interval-ℝ l unit-closed-interval-ℝ)
    interpolation-sequence-intermediate-value-theorem-ℝ n =
      clamp-closed-interval-ℝ
        ( unit-closed-interval-ℝ)
        ( ( map-pointwise-continuous-map-ℝ
            ( f)
            ( sequence-intermediate-value-theorem-ℝ n)) *ℝ
          real-ℚ⁺ (inv-ℚ⁺ ε))

    shift-sequence-intermediate-value-theorem-ℝ : sequence (ℝ⁰⁺ l)
    shift-sequence-intermediate-value-theorem-ℝ n =
      let
        (d , 0≤d , _) = interpolation-sequence-intermediate-value-theorem-ℝ n
      in
        ( d , 0≤d) *ℝ⁰⁺
        ( nonnegative-diff-leq-ℝ a≤b) *ℝ⁰⁺
        ( nonnegative-real-ℚ⁺ (power-ℚ⁺ (succ-ℕ n) one-half-ℚ⁺))

    lower-bound-sequence-intermediate-value-theorem-ℝ 0 = a
    lower-bound-sequence-intermediate-value-theorem-ℝ (succ-ℕ n) =
      ( sequence-intermediate-value-theorem-ℝ n) -ℝ
      ( real-ℝ⁰⁺ (shift-sequence-intermediate-value-theorem-ℝ n))

    upper-bound-sequence-intermediate-value-theorem-ℝ 0 = b
    upper-bound-sequence-intermediate-value-theorem-ℝ (succ-ℕ n) =
      ( upper-bound-sequence-intermediate-value-theorem-ℝ n) -ℝ
      ( real-ℝ⁰⁺ (shift-sequence-intermediate-value-theorem-ℝ n))
```

### `aₙ ≤ cₙ ≤ bₙ`

```agda
  interleaved mutual
    leq-lower-upper-bound-sequence-intermediate-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)

    is-lower-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( sequence-intermediate-value-theorem-ℝ n)
    is-lower-bound-sequence-intermediate-value-theorem-ℝ n =
      leq-binary-mean-leq-both-ℝ _ _ _
        ( refl-leq-ℝ (lower-bound-sequence-intermediate-value-theorem-ℝ n))
        ( leq-lower-upper-bound-sequence-intermediate-theorem-ℝ n)

    is-upper-bound-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) →
      leq-ℝ
        ( sequence-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)
    is-upper-bound-sequence-intermediate-value-theorem-ℝ n =
      geq-binary-mean-geq-both-ℝ _ _ _
        ( leq-lower-upper-bound-sequence-intermediate-theorem-ℝ n)
        ( refl-leq-ℝ (upper-bound-sequence-intermediate-value-theorem-ℝ n))

    leq-lower-upper-bound-sequence-intermediate-theorem-ℝ 0 = a≤b
    leq-lower-upper-bound-sequence-intermediate-theorem-ℝ (succ-ℕ n) =
      preserves-leq-right-add-ℝ _ _ _
        ( is-upper-bound-sequence-intermediate-value-theorem-ℝ n)
```

### `aₙ` is increasing

```agda
  abstract
    is-increasing-lower-bound-sequence-intermediate-value-theorem-ℝ :
      is-increasing-sequence-Poset
        ( ℝ-Poset l)
        ( lower-bound-sequence-intermediate-value-theorem-ℝ)
    is-increasing-lower-bound-sequence-intermediate-value-theorem-ℝ = {!   !}
```

### `bₙ` is decreasing

```agda
  abstract
    is-decreasing-upper-bound-sequence-intermediate-value-theorem-ℝ :
      is-decreasing-sequence-Poset
        ( ℝ-Poset l)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ)
    is-decreasing-upper-bound-sequence-intermediate-value-theorem-ℝ =
      is-decreasing-leq-succ-sequence-Poset
        ( ℝ-Poset l)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ)
        ( λ n →
          leq-diff-real-ℝ⁰⁺
            ( upper-bound-sequence-intermediate-value-theorem-ℝ n)
            ( shift-sequence-intermediate-value-theorem-ℝ n))
```

### `a ≤ cₙ ≤ b`

```agda
  abstract
    lower-bound-of-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) → leq-ℝ a (sequence-intermediate-value-theorem-ℝ n)
    lower-bound-of-sequence-intermediate-value-theorem-ℝ n =
      transitive-leq-ℝ
        ( a)
        ( lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( sequence-intermediate-value-theorem-ℝ n)
        ( is-lower-bound-sequence-intermediate-value-theorem-ℝ n)
        ( is-increasing-lower-bound-sequence-intermediate-value-theorem-ℝ
          ( 0)
          ( n)
          ( leq-zero-ℕ n))

    upper-bound-of-sequence-intermediate-value-theorem-ℝ :
      (n : ℕ) → leq-ℝ (sequence-intermediate-value-theorem-ℝ n) b
    upper-bound-of-sequence-intermediate-value-theorem-ℝ n =
      transitive-leq-ℝ
        ( sequence-intermediate-value-theorem-ℝ n)
        ( upper-bound-sequence-intermediate-value-theorem-ℝ n)
        ( b)
        ( is-decreasing-upper-bound-sequence-intermediate-value-theorem-ℝ
          ( 0)
          ( n)
          ( leq-zero-ℕ n))
        ( is-upper-bound-sequence-intermediate-value-theorem-ℝ n)
```

### `bₙ - aₙ = (b - a)/2ⁿ`

```agda
  abstract
    interleaved mutual
      diff-upper-lower-bound-sequence-intermediate-value-theorem-ℝ :
        (n : ℕ) →
        ( ( upper-bound-sequence-intermediate-value-theorem-ℝ n) -ℝ
          ( lower-bound-sequence-intermediate-value-theorem-ℝ n)) ＝
        ( (b -ℝ a) *ℝ real-ℚ (rational-power-ℚ⁺ n one-half-ℚ⁺))
      diff-upper-lower-bound-sequence-intermediate-value-theorem-ℝ = {!   !}

      diff-upper-bound-sequence-intermediate-value-theorem-ℝ :
        (n : ℕ) →
        ( ( upper-bound-sequence-intermediate-value-theorem-ℝ n) -ℝ
          ( sequence-intermediate-value-theorem-ℝ n)) ＝
        ( (b -ℝ a) *ℝ real-ℚ (rational-power-ℚ⁺ (succ-ℕ n) one-half-ℚ⁺))
      diff-upper-bound-sequence-intermediate-value-theorem-ℝ = {!   !}
```

### The `cₙ` are a Cauchy sequence with a limit `c`

```agda
  abstract
    is-cauchy-sequence-intermediate-value-theorem-ℝ :
      is-cauchy-sequence-ℝ sequence-intermediate-value-theorem-ℝ
    is-cauchy-sequence-intermediate-value-theorem-ℝ =
      {!   !}

  cauchy-sequence-intermediate-value-theorem-ℝ : cauchy-sequence-ℝ l
  cauchy-sequence-intermediate-value-theorem-ℝ =
    ( sequence-intermediate-value-theorem-ℝ ,
      is-cauchy-sequence-intermediate-value-theorem-ℝ)

  lim-cauchy-sequence-intermediate-value-theorem-ℝ : ℝ l
  lim-cauchy-sequence-intermediate-value-theorem-ℝ =
    lim-cauchy-sequence-ℝ cauchy-sequence-intermediate-value-theorem-ℝ

  abstract
    is-limit-lim-cauchy-sequence-intermediate-value-theorem-ℝ :
      is-limit-sequence-ℝ
        ( sequence-intermediate-value-theorem-ℝ)
        ( lim-cauchy-sequence-intermediate-value-theorem-ℝ)
    is-limit-lim-cauchy-sequence-intermediate-value-theorem-ℝ =
      is-limit-lim-cauchy-sequence-ℝ
        ( cauchy-sequence-intermediate-value-theorem-ℝ)
```

### `a ≤ c ≤ b`

```agda
  abstract
    lower-bound-lim-cauchy-sequence-intermediate-value-theorem-ℝ :
      leq-ℝ a lim-cauchy-sequence-intermediate-value-theorem-ℝ
    lower-bound-lim-cauchy-sequence-intermediate-value-theorem-ℝ =
      lower-bound-lim-lower-bound-sequence-ℝ
        ( a)
        ( lower-bound-of-sequence-intermediate-value-theorem-ℝ)
        ( is-limit-lim-cauchy-sequence-intermediate-value-theorem-ℝ)

    upper-bound-lim-cauchy-sequence-intermediate-value-theorem-ℝ :
      leq-ℝ lim-cauchy-sequence-intermediate-value-theorem-ℝ b
    upper-bound-lim-cauchy-sequence-intermediate-value-theorem-ℝ =
      upper-bound-lim-upper-bound-sequence-ℝ
        ( b)
        ( upper-bound-of-sequence-intermediate-value-theorem-ℝ)
        ( is-limit-lim-cauchy-sequence-intermediate-value-theorem-ℝ)
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
              ( sequence-intermediate-value-theorem-ℝ n)))
          ( real-ℚ⁺ ε)))) ∨
    ( ( is-negative-prop-ℝ
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( lower-bound-sequence-intermediate-value-theorem-ℝ m))) ∧
      ( is-positive-prop-ℝ
        ( map-pointwise-continuous-map-ℝ
          ( f)
          ( upper-bound-sequence-intermediate-value-theorem-ℝ m))))

  abstract
    lemma-intermediate-value-theorem-ℝ :
      (m : ℕ) → type-Prop (lemma-prop-intermediate-value-theorem-ℝ m)
    lemma-intermediate-value-theorem-ℝ 0 = inr-disjunction (fa<0 , 0<fb)
    lemma-intermediate-value-theorem-ℝ (succ-ℕ m) =
      let
        motive = lemma-prop-intermediate-value-theorem-ℝ (succ-ℕ m)
        ε' = one-half-ℚ⁺ *ℚ⁺ ε
        ε'<ε = le-left-mul-less-than-one-ℚ⁺ one-half-ℚ⁺ le-one-half-one-ℚ ε
        fcₘ =
          map-pointwise-continuous-map-ℝ
            ( f)
            ( sequence-intermediate-value-theorem-ℝ m)
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
                    let
                      dₘ=1 :
                        sim-ℝ
                          ( pr1
                            ( interpolation-sequence-intermediate-value-theorem-ℝ
                              ( m)))
                          ( one-ℝ)
                      dₘ=1 = {!   !}
                    in
                      inr-disjunction
                        ( {!   !} ,
                          {!   !}))
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
                  ( {!   !} ,
                    {!   !}))
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
        open do-syntax-trunc-Prop motive
      in do
        (μf , is-mod-μf) ←
          is-pointwise-continuous-map-pointwise-continuous-map-ℝ
            ( f)
            ( lim-cauchy-sequence-intermediate-value-theorem-ℝ)
        let δ = one-half-ℚ⁺ *ℚ⁺ μf ε
        (μseq , is-mod-μseq) ←
          is-limit-lim-cauchy-sequence-ℝ
            ( cauchy-sequence-intermediate-value-theorem-ℝ)
        (m₁ , ½ᵐ<δ) ←
          arbitrarily-small-power-le-one-ℚ⁺
            ( one-half-ℚ⁺)
            ( δ)
            ( le-one-half-one-ℚ)
        let
          m₂ = μseq δ
          m = max-ℕ m₁ m₂
        elim-disjunction
          ( motive)
          ( λ ∃n:|cₙ|≤ε → do
            (n , n≤m , |cₙ|≤ε) ← ∃n:|cₙ|≤ε
            intro-exists
              ( sequence-intermediate-value-theorem-ℝ n ,
                lower-bound-of-sequence-intermediate-value-theorem-ℝ n ,
                upper-bound-of-sequence-intermediate-value-theorem-ℝ n)
              ( |cₙ|≤ε))
          ( λ (faₘ<0 , 0<fbₘ) →
            intro-exists
              ( lim-cauchy-sequence-intermediate-value-theorem-ℝ ,
                lower-bound-lim-cauchy-sequence-intermediate-value-theorem-ℝ ,
                upper-bound-lim-cauchy-sequence-intermediate-value-theorem-ℝ)
              ( leq-abs-leq-leq-neg-ℝ'
                {!   !}
                {!   !}))
          ( lemma-intermediate-value-theorem-ℝ m)
```

## External links

- [Intermediate value theorem](https://ncatlab.org/nlab/show/intermediate+value+theorem)
  on $n$Lab
- [Intermediate value theorem](https://en.wikipedia.org/wiki/Intermediate_value_theorem)
  on Wikipedia

## References

{{#bibliography}}
