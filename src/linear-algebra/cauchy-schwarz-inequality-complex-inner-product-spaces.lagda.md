# The Cauchy-Schwarz inequality for complex inner product spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.cauchy-schwarz-inequality-complex-inner-product-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.magnitude-complex-numbers
open import complex-numbers.multiplication-complex-numbers

open import elementary-number-theory.integers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.complex-inner-product-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-positive-and-negative-real-numbers
open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
```

</details>

## Idea

The
{{#concept "Cauchy-Schwarz inequality" WDID=Q190546 WD="Cauchy-Schwarz inequality" Disambiguation="in complex inner product spaces" Agda=cauchy-schwarz-inequality-ℂ-Inner-Product-Space}}
states that for any `u` and `v` in a
[complex inner product space](linear-algebra.complex-inner-product-spaces.md),
the [magnitude](complex-numbers.magnitude-complex-numbers.md) of the inner
product of `u` and `v` is at most the product of the norms of `u` and `v`.

The Cauchy-Schwarz inequality is the [78th](literature.100-theorems.md#78)
theorem on [Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Proof

### If `∥u∥² ≤ 1` and `∥v∥² ≤ 1`, then `|⟨u,v⟩|² ≤ 1`

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    leq-one-squared-magnitude-inner-product-leq-one-squared-norm-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) →
      leq-ℝ (squared-norm-ℂ-Inner-Product-Space V u) one-ℝ →
      leq-ℝ (squared-norm-ℂ-Inner-Product-Space V v) one-ℝ →
      leq-ℝ
        ( squared-magnitude-ℂ (inner-product-ℂ-Inner-Product-Space V u v))
        ( one-ℝ)
    leq-one-squared-magnitude-inner-product-leq-one-squared-norm-ℂ-Inner-Product-Space
      u v ∥u∥²≤1 ∥v∥²≤1 =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        _*V_ = mul-ℂ-Inner-Product-Space V
        _-V_ = diff-ℂ-Inner-Product-Space V
        _·V_ = inner-product-ℂ-Inner-Product-Space V
        w = (u ·V v) *V v
      in
        leq-is-nonnegative-diff-ℝ _ _
          ( chain-of-inequalities
            zero-ℝ
            ≤ squared-norm-ℂ-Inner-Product-Space V (u -V w)
              by is-nonnegative-squared-norm-ℂ-Inner-Product-Space V (u -V w)
            ≤ ( squared-norm-ℂ-Inner-Product-Space V u) -ℝ
              ( real-ℕ 2 *ℝ re-ℂ (u ·V w)) +ℝ
              ( squared-norm-ℂ-Inner-Product-Space V w)
              by leq-eq-ℝ (squared-norm-diff-ℂ-Inner-Product-Space V u w)
            ≤ ( squared-norm-ℂ-Inner-Product-Space V u) -ℝ
              ( real-ℕ 2 *ℝ squared-magnitude-ℂ (u ·V v)) +ℝ
              ( ( squared-magnitude-ℂ (u ·V v)) *ℝ
                ( squared-norm-ℂ-Inner-Product-Space V v))
              by
                leq-eq-ℝ
                  ( ap-add-ℝ
                    ( ap-diff-ℝ
                      ( refl)
                      ( ap-mul-ℝ
                        ( refl)
                        ( ap
                          ( re-ℂ)
                          ( ( conjugates-scalar-mul-right-inner-product-ℂ-Inner-Product-Space
                              ( V)
                              ( _)
                              ( u)
                              ( v)) ∙
                            ( commutative-mul-ℂ _ _) ∙
                            ( eq-squared-magnitude-mul-conjugate-ℂ (u ·V v))))))
                    ( squared-norm-mul-ℂ-Inner-Product-Space V _ _))
            ≤ ( one-ℝ) -ℝ
              ( real-ℕ 2 *ℝ squared-magnitude-ℂ (u ·V v)) +ℝ
              ( squared-magnitude-ℂ (u ·V v) *ℝ one-ℝ)
              by
                preserves-leq-add-ℝ
                  ( preserves-leq-right-add-ℝ _ _ _ ∥u∥²≤1)
                  ( preserves-leq-left-mul-ℝ⁰⁺
                    ( nonnegative-squared-magnitude-ℂ (u ·V v))
                    ( ∥v∥²≤1))
            ≤ ( one-ℝ) +ℝ
              ( neg-ℝ (real-ℕ 2) *ℝ squared-magnitude-ℂ (u ·V v)) +ℝ
              ( one-ℝ *ℝ squared-magnitude-ℂ (u ·V v))
              by
                leq-eq-ℝ
                  ( ap-add-ℝ
                    ( ap-add-ℝ refl (inv (left-negative-law-mul-ℝ _ _)))
                    ( commutative-mul-ℝ _ _))
            ≤ ( one-ℝ) +ℝ
              ( ( neg-ℝ (real-ℕ 2) *ℝ squared-magnitude-ℂ (u ·V v)) +ℝ
                ( one-ℝ *ℝ squared-magnitude-ℂ (u ·V v)))
              by leq-eq-ℝ (associative-add-ℝ _ _ _)
            ≤ one-ℝ -ℝ squared-magnitude-ℂ (u ·V v)
              by
                leq-eq-ℝ
                  ( ap-add-ℝ
                    ( refl)
                    ( equational-reasoning
                      ( neg-ℝ (real-ℕ 2) *ℝ squared-magnitude-ℂ (u ·V v)) +ℝ
                      ( one-ℝ *ℝ squared-magnitude-ℂ (u ·V v))
                      ＝
                        ( neg-ℝ (real-ℕ 2) +ℝ one-ℝ) *ℝ
                        ( squared-magnitude-ℂ (u ·V v))
                        by
                          inv
                            ( right-distributive-mul-add-ℝ
                              ( neg-ℝ (real-ℕ 2))
                              ( one-ℝ)
                              ( squared-magnitude-ℂ (u ·V v)))
                      ＝
                        ( real-ℤ (neg-ℤ (int-ℕ 2)) +ℝ real-ℤ one-ℤ) *ℝ
                        ( squared-magnitude-ℂ (u ·V v))
                        by
                          ap-mul-ℝ
                            ( ap-add-ℝ
                              ( neg-real-ℤ (int-ℕ 2))
                              ( refl {x = one-ℝ}))
                            ( refl)
                      ＝ real-ℤ neg-one-ℤ *ℝ squared-magnitude-ℂ (u ·V v)
                        by ap-mul-ℝ (add-real-ℤ _ _) refl
                      ＝ neg-ℝ (squared-magnitude-ℂ (u ·V v))
                        by left-neg-one-law-mul-ℝ _)))
```

### If `∥u∥ ≤ 1` and `∥v∥ ≤ 1`, then `|⟨u,v⟩| ≤ 1`

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    leq-one-magnitude-inner-product-leq-one-norm-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) →
      leq-ℝ (map-norm-ℂ-Inner-Product-Space V u) one-ℝ →
      leq-ℝ (map-norm-ℂ-Inner-Product-Space V v) one-ℝ →
      leq-ℝ
        ( magnitude-ℂ (inner-product-ℂ-Inner-Product-Space V u v))
        ( one-ℝ)
    leq-one-magnitude-inner-product-leq-one-norm-ℂ-Inner-Product-Space
      u v ∥u∥≤1 ∥v∥≤1 =
      tr
        ( leq-ℝ _)
        ( real-sqrt-one-ℝ⁰⁺)
        ( preserves-leq-sqrt-ℝ⁰⁺
          ( nonnegative-squared-magnitude-ℂ
            ( inner-product-ℂ-Inner-Product-Space V u v))
          ( one-ℝ⁰⁺)
          ( leq-one-squared-magnitude-inner-product-leq-one-squared-norm-ℂ-Inner-Product-Space
            ( V)
            ( u)
            ( v)
            ( leq-one-leq-one-sqrt-ℝ⁰⁺
              ( nonnegative-squared-norm-ℂ-Inner-Product-Space V u)
              ( ∥u∥≤1))
            ( leq-one-leq-one-sqrt-ℝ⁰⁺
              ( nonnegative-squared-norm-ℂ-Inner-Product-Space V v)
              ( ∥v∥≤1))))
```

### For any `v` in an inner product space, the norm of `(∥v∥ + ε)⁻¹ v` is at most `1`

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    leq-norm-mul-inv-norm-plus-positive-rational-ℂ-Inner-Product-Space :
      (v : type-ℂ-Inner-Product-Space V) (ε : ℚ⁺) →
      leq-ℝ
        ( map-norm-ℂ-Inner-Product-Space
          ( V)
          ( mul-real-ℂ-Inner-Product-Space
            ( V)
            ( real-inv-ℝ⁺
              ( add-nonnegative-positive-ℝ
                ( nonnegative-norm-ℂ-Inner-Product-Space V v)
                ( positive-real-ℚ⁺ ε)))
            ( v)))
        ( one-ℝ)
    leq-norm-mul-inv-norm-plus-positive-rational-ℂ-Inner-Product-Space v ε =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
        map-norm-ℂ-Inner-Product-Space V
          ( mul-real-ℂ-Inner-Product-Space V
            ( real-inv-ℝ⁺
              ( add-nonnegative-positive-ℝ
                ( nonnegative-norm-ℂ-Inner-Product-Space V v)
                ( positive-real-ℚ⁺ ε)))
            ( v))
        ≤ ( abs-ℝ
            ( real-inv-ℝ⁺
              ( add-nonnegative-positive-ℝ
                ( nonnegative-norm-ℂ-Inner-Product-Space V v)
                ( positive-real-ℚ⁺ ε)))) *ℝ
          ( map-norm-ℂ-Inner-Product-Space V v)
          by leq-eq-ℝ (norm-mul-real-ℂ-Inner-Product-Space V _ v)
        ≤ ( real-inv-ℝ⁺
            ( add-nonnegative-positive-ℝ
              ( nonnegative-norm-ℂ-Inner-Product-Space V v)
              ( positive-real-ℚ⁺ ε))) *ℝ
          ( map-norm-ℂ-Inner-Product-Space V v)
          by leq-eq-ℝ (ap-mul-ℝ (abs-real-ℝ⁺ (inv-ℝ⁺ _)) refl)
        ≤ one-ℝ
          by
            leq-one-mul-inv-add-positive-ℝ⁰⁺
              ( nonnegative-norm-ℂ-Inner-Product-Space V v)
              ( positive-real-ℚ⁺ ε)
```

### For any `u`, `v` in a complex inner product space and any positive rational `δ`, `ε`, `|⟨u,v⟩| ≤ (∥u∥ + δ)(∥v∥ + ε)`

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    approx-cauchy-schwarz-inequality-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) (δ ε : ℚ⁺) →
      leq-ℝ
        ( magnitude-ℂ (inner-product-ℂ-Inner-Product-Space V u v))
        ( ( map-norm-ℂ-Inner-Product-Space V u +ℝ real-ℚ⁺ δ) *ℝ
          ( map-norm-ℂ-Inner-Product-Space V v +ℝ real-ℚ⁺ ε))
    approx-cauchy-schwarz-inequality-ℂ-Inner-Product-Space u v δ ε =
      let
        ∥u∥+δ =
          add-nonnegative-positive-ℝ
            ( nonnegative-norm-ℂ-Inner-Product-Space V u)
            ( positive-real-ℚ⁺ δ)
        ∥v∥+ε =
          add-nonnegative-positive-ℝ
            ( nonnegative-norm-ℂ-Inner-Product-Space V v)
            ( positive-real-ℚ⁺ ε)
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        _ℝ*V_ = mul-real-ℂ-Inner-Product-Space V
        _·V_ = inner-product-ℂ-Inner-Product-Space V
      in
        chain-of-inequalities
          magnitude-ℂ (u ·V v)
          ≤ real-ℝ⁺ ∥u∥+δ *ℝ (real-inv-ℝ⁺ ∥u∥+δ *ℝ magnitude-ℂ (u ·V v))
            by leq-sim-ℝ' (cancel-left-mul-div-ℝ⁺ _ _)
          ≤ ( real-ℝ⁺ ∥u∥+δ) *ℝ
            ( magnitude-ℂ (complex-ℝ (real-inv-ℝ⁺ ∥u∥+δ) *ℂ (u ·V v)))
            by
              leq-eq-ℝ
                ( ap-mul-ℝ
                  ( refl)
                  ( inv (magnitude-left-mul-complex-ℝ⁺ (inv-ℝ⁺ ∥u∥+δ) _)))
          ≤ ( real-ℝ⁺ ∥u∥+δ) *ℝ
            ( magnitude-ℂ ((real-inv-ℝ⁺ ∥u∥+δ ℝ*V u) ·V v))
            by
              leq-eq-ℝ
                ( ap-mul-ℝ
                  ( refl)
                  ( ap
                    ( magnitude-ℂ)
                    ( inv
                      ( preserves-scalar-mul-left-inner-product-ℂ-Inner-Product-Space
                        ( V)
                        ( _)
                        ( u)
                        ( v)))))
          ≤ ( real-ℝ⁺ ∥u∥+δ) *ℝ
            ( ( real-ℝ⁺ ∥v∥+ε) *ℝ
              ( ( real-inv-ℝ⁺ ∥v∥+ε) *ℝ
                ( magnitude-ℂ ((real-inv-ℝ⁺ ∥u∥+δ ℝ*V u) ·V v))))
            by
              leq-sim-ℝ'
                ( preserves-sim-left-mul-ℝ _ _ _
                  ( cancel-left-mul-div-ℝ⁺ ∥v∥+ε (magnitude-ℂ _)))
          ≤ ( real-ℝ⁺ ∥u∥+δ) *ℝ
            ( ( real-ℝ⁺ ∥v∥+ε) *ℝ
                ( magnitude-ℂ
                  ( ( real-inv-ℝ⁺ ∥u∥+δ ℝ*V u) ·V
                    ( real-inv-ℝ⁺ ∥v∥+ε ℝ*V v))))
            by
              leq-eq-ℝ
                ( ap-mul-ℝ
                  ( refl)
                  ( ap-mul-ℝ
                    ( refl)
                    ( equational-reasoning
                      ( real-inv-ℝ⁺ ∥v∥+ε) *ℝ
                      ( magnitude-ℂ ((real-inv-ℝ⁺ ∥u∥+δ ℝ*V u) ·V v))
                      ＝ magnitude-ℂ
                          ( ( complex-ℝ (real-inv-ℝ⁺ ∥v∥+ε)) *ℂ
                            ( (real-inv-ℝ⁺ ∥u∥+δ ℝ*V u) ·V v))
                        by inv (magnitude-left-mul-complex-ℝ⁺ (inv-ℝ⁺ ∥v∥+ε) _)
                      ＝
                        magnitude-ℂ
                          ( ( real-inv-ℝ⁺ ∥u∥+δ ℝ*V u) ·V
                            ( real-inv-ℝ⁺ ∥v∥+ε ℝ*V v))
                        by
                          ap
                            ( magnitude-ℂ)
                            ( inv
                              ( preserves-scalar-mul-real-right-inner-product-ℂ-Inner-Product-Space
                                ( V)
                                ( real-inv-ℝ⁺ ∥v∥+ε)
                                ( real-inv-ℝ⁺ ∥u∥+δ ℝ*V u)
                                ( v))))))
          ≤ real-ℝ⁺ ∥u∥+δ *ℝ (real-ℝ⁺ ∥v∥+ε *ℝ one-ℝ)
            by
              preserves-leq-left-mul-ℝ⁺
                ( ∥u∥+δ)
                ( preserves-leq-left-mul-ℝ⁺
                  ( ∥v∥+ε)
                  ( leq-one-magnitude-inner-product-leq-one-norm-ℂ-Inner-Product-Space
                    ( V)
                    ( real-inv-ℝ⁺ ∥u∥+δ ℝ*V u)
                    ( real-inv-ℝ⁺ ∥v∥+ε ℝ*V v)
                    ( leq-norm-mul-inv-norm-plus-positive-rational-ℂ-Inner-Product-Space
                      ( V)
                      ( u)
                      ( δ))
                    ( leq-norm-mul-inv-norm-plus-positive-rational-ℂ-Inner-Product-Space
                      ( V)
                      ( v)
                      ( ε))))
          ≤ real-ℝ⁺ ∥u∥+δ *ℝ real-ℝ⁺ ∥v∥+ε
            by leq-eq-ℝ (ap-mul-ℝ refl (right-unit-law-mul-ℝ _))
```

### For any `u`, `v` in a complex inner product space, `|⟨u,v⟩| ≤ ∥u∥ ∥v∥`

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    cauchy-schwarz-inequality-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) →
      leq-ℝ
        ( magnitude-ℂ (inner-product-ℂ-Inner-Product-Space V u v))
        ( ( map-norm-ℂ-Inner-Product-Space V) u *ℝ
          ( map-norm-ℂ-Inner-Product-Space V v))
    cauchy-schwarz-inequality-ℂ-Inner-Product-Space u v =
      saturated-leq-mul-ℝ⁰⁺
        ( nonnegative-magnitude-ℂ (inner-product-ℂ-Inner-Product-Space V u v))
        ( nonnegative-norm-ℂ-Inner-Product-Space V u)
        ( nonnegative-norm-ℂ-Inner-Product-Space V v)
        ( approx-cauchy-schwarz-inequality-ℂ-Inner-Product-Space V u v)
```

## See also

- [The Cauchy-Schwarz inequality in real inner product spaces](linear-algebra.cauchy-schwarz-inequality-real-inner-product-spaces.md)

## External links

- [Cauchy-Schwarz inequality](https://en.wikipedia.org/wiki/Cauchy%E2%80%93Schwarz_inequality)
  on Wikipedia
