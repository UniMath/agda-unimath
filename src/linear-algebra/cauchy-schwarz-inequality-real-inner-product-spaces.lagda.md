# The Cauchy-Schwarz inequality on real inner product spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.cauchy-schwarz-inequality-real-inner-product-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import linear-algebra.orthogonality-real-inner-product-spaces
open import linear-algebra.real-inner-product-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-positive-and-negative-real-numbers
open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-and-negative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.saturation-inequality-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

The
{{#concept "Cauchy-Schwarz inequality" WDID=Q190546 WD="Cauchy-Schwarz inequality" Disambiguation="in real inner product spaces" Agda=cauchy-schwarz-inequality-ℝ-Inner-Product-Space}}
states that for any `u` and `v` in a
[real inner product space](linear-algebra.real-inner-product-spaces.md), the
[absolute value](real-numbers.absolute-value-real-numbers.md) of the inner
product of `u` and `v` is at most the product of the norms of `u` and `v`.

The Cauchy-Schwarz inequality is the [78th](literature.100-theorems.md#78)
theorem on [Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Proof

### If `∥u∥² ≤ 1` and `∥v∥² ≤ 1`, then `|⟨u,v⟩| ≤ 1`

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    leq-one-inner-product-leq-one-squared-norm-ℝ-Inner-Product-Space :
      (u v : type-ℝ-Inner-Product-Space V) →
      leq-ℝ (squared-norm-ℝ-Inner-Product-Space V u) one-ℝ →
      leq-ℝ (squared-norm-ℝ-Inner-Product-Space V v) one-ℝ →
      leq-ℝ (inner-product-ℝ-Inner-Product-Space V u v) one-ℝ
    leq-one-inner-product-leq-one-squared-norm-ℝ-Inner-Product-Space
      u v ∥u∥²≤1 ∥v∥²≤1 =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        leq-is-nonnegative-diff-ℝ _ _
          ( is-nonnegative-is-nonnegative-left-mul-ℝ⁺
            ( positive-real-ℕ⁺ (2 , λ ()))
            ( chain-of-inequalities
              zero-ℝ
              ≤ squared-norm-ℝ-Inner-Product-Space V
                  ( diff-ℝ-Inner-Product-Space V u v)
                by
                  is-nonnegative-diagonal-inner-product-ℝ-Inner-Product-Space
                    ( V)
                    ( _)
              ≤ ( ( squared-norm-ℝ-Inner-Product-Space V u) -ℝ
                  ( real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V u v)) +ℝ
                ( squared-norm-ℝ-Inner-Product-Space V v)
                by leq-eq-ℝ (squared-norm-diff-ℝ-Inner-Product-Space V u v)
              ≤ ( ( squared-norm-ℝ-Inner-Product-Space V u) +ℝ
                  ( squared-norm-ℝ-Inner-Product-Space V v)) -ℝ
                ( real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V u v)
                by leq-eq-ℝ (right-swap-add-ℝ _ _ _)
              ≤ ( one-ℝ +ℝ one-ℝ) -ℝ
                ( real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V u v)
                by
                  preserves-leq-right-add-ℝ _ _ _
                    ( preserves-leq-add-ℝ ∥u∥²≤1 ∥v∥²≤1)
              ≤ ( real-ℕ 2 *ℝ one-ℝ) -ℝ
                ( real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V u v)
                by leq-eq-ℝ (ap-diff-ℝ (inv (left-mul-real-ℕ 2 _)) refl)
              ≤ real-ℕ 2 *ℝ (one-ℝ -ℝ inner-product-ℝ-Inner-Product-Space V u v)
                by leq-eq-ℝ (inv (left-distributive-mul-diff-ℝ _ _ _))))

    leq-one-neg-inner-product-leq-one-squared-norm-ℝ-Inner-Product-Space :
      (u v : type-ℝ-Inner-Product-Space V) →
      leq-ℝ (squared-norm-ℝ-Inner-Product-Space V u) one-ℝ →
      leq-ℝ (squared-norm-ℝ-Inner-Product-Space V v) one-ℝ →
      leq-ℝ (neg-ℝ (inner-product-ℝ-Inner-Product-Space V u v)) one-ℝ
    leq-one-neg-inner-product-leq-one-squared-norm-ℝ-Inner-Product-Space
      u v ∥u∥²≤1 ∥v∥²≤1 =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        leq-is-nonnegative-diff-ℝ _ _
          ( is-nonnegative-is-nonnegative-left-mul-ℝ⁺
            ( positive-real-ℕ⁺ (2 , λ ()))
            ( chain-of-inequalities
              zero-ℝ
              ≤ squared-norm-ℝ-Inner-Product-Space V
                  ( add-ℝ-Inner-Product-Space V u v)
                by
                  is-nonnegative-diagonal-inner-product-ℝ-Inner-Product-Space
                    ( V)
                    ( _)
              ≤ ( squared-norm-ℝ-Inner-Product-Space V u) +ℝ
                ( real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V u v) +ℝ
                ( squared-norm-ℝ-Inner-Product-Space V v)
                by leq-eq-ℝ (squared-norm-add-ℝ-Inner-Product-Space V u v)
              ≤ ( squared-norm-ℝ-Inner-Product-Space V u) +ℝ
                ( squared-norm-ℝ-Inner-Product-Space V v) +ℝ
                ( real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V u v)
                by leq-eq-ℝ (right-swap-add-ℝ _ _ _)
              ≤ ( one-ℝ +ℝ one-ℝ) +ℝ
                ( real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V u v)
                by
                  preserves-leq-right-add-ℝ _ _ _
                    ( preserves-leq-add-ℝ ∥u∥²≤1 ∥v∥²≤1)
              ≤ ( real-ℕ 2 *ℝ one-ℝ) +ℝ
                ( real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V u v)
                by leq-eq-ℝ (ap-add-ℝ (inv (left-mul-real-ℕ 2 one-ℝ)) refl)
              ≤ real-ℕ 2 *ℝ (one-ℝ +ℝ inner-product-ℝ-Inner-Product-Space V u v)
                by leq-eq-ℝ (inv (left-distributive-mul-add-ℝ _ _ _))
              ≤ ( real-ℕ 2) *ℝ
                ( one-ℝ -ℝ neg-ℝ (inner-product-ℝ-Inner-Product-Space V u v))
                by
                  leq-eq-ℝ (ap-mul-ℝ refl (ap-add-ℝ refl (inv (neg-neg-ℝ _))))))

    leq-one-abs-inner-product-leq-one-squared-norm-ℝ-Inner-Product-Space :
      (u v : type-ℝ-Inner-Product-Space V) →
      leq-ℝ (squared-norm-ℝ-Inner-Product-Space V u) one-ℝ →
      leq-ℝ (squared-norm-ℝ-Inner-Product-Space V v) one-ℝ →
      leq-ℝ (abs-ℝ (inner-product-ℝ-Inner-Product-Space V u v)) one-ℝ
    leq-one-abs-inner-product-leq-one-squared-norm-ℝ-Inner-Product-Space
      u v ∥u∥²≤1 ∥v∥²≤1 =
      leq-abs-leq-leq-neg-ℝ
        ( leq-one-inner-product-leq-one-squared-norm-ℝ-Inner-Product-Space
          ( u)
          ( v)
          ( ∥u∥²≤1)
          ( ∥v∥²≤1))
        ( leq-one-neg-inner-product-leq-one-squared-norm-ℝ-Inner-Product-Space
          ( u)
          ( v)
          ( ∥u∥²≤1)
          ( ∥v∥²≤1))
```

### If `∥u∥ ≤ 1` and `∥v∥ ≤ 1`, then `|⟨u,v⟩| ≤ 1`

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    leq-one-abs-inner-product-leq-one-norm-ℝ-Inner-Product-Space :
      (u v : type-ℝ-Inner-Product-Space V) →
      leq-ℝ (norm-ℝ-Inner-Product-Space V u) one-ℝ →
      leq-ℝ (norm-ℝ-Inner-Product-Space V v) one-ℝ →
      leq-ℝ (abs-ℝ (inner-product-ℝ-Inner-Product-Space V u v)) one-ℝ
    leq-one-abs-inner-product-leq-one-norm-ℝ-Inner-Product-Space
      u v ∥u∥≤1 ∥v∥≤1 =
      leq-one-abs-inner-product-leq-one-squared-norm-ℝ-Inner-Product-Space
        ( V)
        ( u)
        ( v)
        ( leq-one-leq-one-sqrt-ℝ⁰⁺
          ( nonnegative-squared-norm-ℝ-Inner-Product-Space V u)
          ( ∥u∥≤1))
        ( leq-one-leq-one-sqrt-ℝ⁰⁺
          ( nonnegative-squared-norm-ℝ-Inner-Product-Space V v)
          ( ∥v∥≤1))
```

### For any `v` in an inner product space, the norm of `(∥v∥ + ε)⁻¹ v` is at most `1`

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    leq-norm-mul-inv-norm-plus-positive-rational-ℝ-Inner-Product-Space :
      (v : type-ℝ-Inner-Product-Space V) (ε : ℚ⁺) →
      leq-ℝ
        ( norm-ℝ-Inner-Product-Space V
          ( mul-ℝ-Inner-Product-Space V
            ( real-inv-ℝ⁺
              ( add-nonnegative-positive-ℝ
                  ( nonnegative-norm-ℝ-Inner-Product-Space V v)
                  ( positive-real-ℚ⁺ ε)))
            ( v)))
        ( one-ℝ)
    leq-norm-mul-inv-norm-plus-positive-rational-ℝ-Inner-Product-Space v ε =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          norm-ℝ-Inner-Product-Space V
            ( mul-ℝ-Inner-Product-Space V
              ( real-inv-ℝ⁺
                ( add-nonnegative-positive-ℝ
                  ( nonnegative-norm-ℝ-Inner-Product-Space V v)
                  ( positive-real-ℚ⁺ ε)))
              ( v))
          ≤ ( real-inv-ℝ⁺
              ( add-nonnegative-positive-ℝ
                ( nonnegative-norm-ℝ-Inner-Product-Space V v)
                ( positive-real-ℚ⁺ ε))) *ℝ
            ( norm-ℝ-Inner-Product-Space V v)
            by
              leq-eq-ℝ
                ( is-positively-homogeneous-norm-ℝ-Inner-Product-Space V
                  ( inv-ℝ⁺
                    ( add-nonnegative-positive-ℝ
                      ( nonnegative-norm-ℝ-Inner-Product-Space V v)
                      ( positive-real-ℚ⁺ ε)))
                  ( v))
          ≤ one-ℝ
            by
              leq-one-mul-inv-add-positive-ℝ⁰⁺
                ( nonnegative-norm-ℝ-Inner-Product-Space V v)
                ( positive-real-ℚ⁺ ε)
```

### For any `u`, `v` in a real inner product space and any positive rational `δ`, `ε`, `|⟨u,v⟩| ≤ (∥u∥ + δ)(∥v∥ + ε)`

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    approx-cauchy-schwarz-inequality-ℝ-Inner-Product-Space :
      (u v : type-ℝ-Inner-Product-Space V) (δ ε : ℚ⁺) →
      leq-ℝ
        ( abs-ℝ (inner-product-ℝ-Inner-Product-Space V u v))
        ( (norm-ℝ-Inner-Product-Space V u +ℝ real-ℚ⁺ δ) *ℝ
          (norm-ℝ-Inner-Product-Space V v +ℝ real-ℚ⁺ ε))
    approx-cauchy-schwarz-inequality-ℝ-Inner-Product-Space
      u v δ ε =
      let
        ∥u∥+δ =
          add-nonnegative-positive-ℝ
            ( nonnegative-norm-ℝ-Inner-Product-Space V u)
            ( positive-real-ℚ⁺ δ)
        ∥v∥+ε =
          add-nonnegative-positive-ℝ
            ( nonnegative-norm-ℝ-Inner-Product-Space V v)
            ( positive-real-ℚ⁺ ε)
      in
        binary-tr
          ( leq-ℝ)
          ( equational-reasoning
            ( real-ℝ⁺ (∥u∥+δ *ℝ⁺ ∥v∥+ε)) *ℝ
            ( abs-ℝ
              ( inner-product-ℝ-Inner-Product-Space V
                ( mul-ℝ-Inner-Product-Space V (real-inv-ℝ⁺ ∥u∥+δ) u)
                ( mul-ℝ-Inner-Product-Space V (real-inv-ℝ⁺ ∥v∥+ε) v)))
            ＝
              ( real-ℝ⁺ (∥u∥+δ *ℝ⁺ ∥v∥+ε)) *ℝ
              ( abs-ℝ
                ( ( real-inv-ℝ⁺ ∥u∥+δ *ℝ real-inv-ℝ⁺ ∥v∥+ε) *ℝ
                  ( inner-product-ℝ-Inner-Product-Space V u v)))
              by
                ap-mul-ℝ
                  ( refl)
                  ( ap
                    ( abs-ℝ)
                    ( preserves-scalar-mul-inner-product-ℝ-Inner-Product-Space
                      ( V)
                      ( _)
                      ( _)
                      ( _)
                      ( _)))
            ＝
              ( real-ℝ⁺ (∥u∥+δ *ℝ⁺ ∥v∥+ε)) *ℝ
              ( ( real-inv-ℝ⁺ ∥u∥+δ *ℝ real-inv-ℝ⁺ ∥v∥+ε) *ℝ
                ( abs-ℝ (inner-product-ℝ-Inner-Product-Space V u v)))
              by
                ap-mul-ℝ
                  ( refl)
                  ( abs-left-mul-positive-ℝ (inv-ℝ⁺ ∥u∥+δ *ℝ⁺ inv-ℝ⁺ ∥v∥+ε) _)
            ＝
              ( real-ℝ⁺ (∥u∥+δ *ℝ⁺ ∥v∥+ε)) *ℝ
              ( ( real-inv-ℝ⁺ (∥u∥+δ *ℝ⁺ ∥v∥+ε)) *ℝ
                ( abs-ℝ (inner-product-ℝ-Inner-Product-Space V u v)))
              by
                ap-mul-ℝ
                  ( refl)
                  ( ap-mul-ℝ
                    ( inv (distributive-real-inv-mul-ℝ⁺ ∥u∥+δ ∥v∥+ε))
                    ( refl))
            ＝ abs-ℝ (inner-product-ℝ-Inner-Product-Space V u v)
              by eq-sim-ℝ (cancel-left-mul-div-ℝ⁺ (∥u∥+δ *ℝ⁺ ∥v∥+ε) _))
          ( right-unit-law-mul-ℝ _)
          ( preserves-leq-left-mul-ℝ⁺
            ( ∥u∥+δ *ℝ⁺ ∥v∥+ε)
            ( leq-one-abs-inner-product-leq-one-norm-ℝ-Inner-Product-Space
              ( V)
              ( mul-ℝ-Inner-Product-Space V (real-inv-ℝ⁺ ∥u∥+δ) u)
              ( mul-ℝ-Inner-Product-Space V (real-inv-ℝ⁺ ∥v∥+ε) v)
              ( leq-norm-mul-inv-norm-plus-positive-rational-ℝ-Inner-Product-Space
                ( V)
                ( u)
                ( δ))
              ( leq-norm-mul-inv-norm-plus-positive-rational-ℝ-Inner-Product-Space
                ( V)
                ( v)
                ( ε))))
```

### For any `u`, `v` in a real inner product space, `|⟨u,v⟩| ≤ ∥u∥ ∥v∥`

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    cauchy-schwarz-inequality-ℝ-Inner-Product-Space :
      (u v : type-ℝ-Inner-Product-Space V) →
      leq-ℝ
        ( abs-ℝ (inner-product-ℝ-Inner-Product-Space V u v))
        ( ( norm-ℝ-Inner-Product-Space V u) *ℝ
          ( norm-ℝ-Inner-Product-Space V v))
    cauchy-schwarz-inequality-ℝ-Inner-Product-Space u v =
      saturated-leq-mul-ℝ⁰⁺
        ( nonnegative-abs-ℝ (inner-product-ℝ-Inner-Product-Space V u v))
        ( nonnegative-norm-ℝ-Inner-Product-Space V u)
        ( nonnegative-norm-ℝ-Inner-Product-Space V v)
        ( approx-cauchy-schwarz-inequality-ℝ-Inner-Product-Space V u v)
```

## See also

- [The Cauchy-Schwarz inequality in complex inner product spaces](linear-algebra.cauchy-schwarz-inequality-complex-inner-product-spaces.md)

## External links

- [Cauchy-Schwarz inequality](https://en.wikipedia.org/wiki/Cauchy%E2%80%93Schwarz_inequality)
  on Wikipedia
