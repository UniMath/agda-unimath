# Lipschitz continuity of scalar multiplication in normed real vector spaces

```agda
module linear-algebra.lipschitz-continuity-scalar-multiplication-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.lipschitz-maps-normed-real-vector-spaces
open import linear-algebra.normed-real-vector-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
```

</details>

## Idea

Scalar multiplication in
[normed real vector spaces](linear-algebra.normed-real-vector-spaces.md) is
[Lipschitz continuous](linear-algebra.lipschitz-maps-normed-real-vector-spaces.md)
in each argument.

## Properties

### Given a constant `c`, `v ↦ cv` is Lipschitz continuous

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (c : ℝ l1)
  where abstract

  is-lipschitz-left-mul-Normed-ℝ-Vector-Space :
    is-lipschitz-map-Normed-ℝ-Vector-Space V V (mul-Normed-ℝ-Vector-Space V c)
  is-lipschitz-left-mul-Normed-ℝ-Vector-Space =
    is-lipschitz-real-constant-map-Normed-ℝ-Vector-Space
      ( V)
      ( V)
      ( mul-Normed-ℝ-Vector-Space V c)
      ( nonnegative-abs-ℝ c)
      ( λ x y → leq-eq-ℝ (multiplicative-dist-Normed-ℝ-Vector-Space V c x y))
```

### Given a constant vector `v`, `c ↦ cv` is Lipschitz continuous

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (v : type-Normed-ℝ-Vector-Space V)
  where abstract

  is-lipschitz-right-mul-Normed-ℝ-Vector-Space :
    is-lipschitz-map-Normed-ℝ-Vector-Space
      ( normed-real-vector-space-ℝ l1)
      ( V)
      ( λ c → mul-Normed-ℝ-Vector-Space V c v)
  is-lipschitz-right-mul-Normed-ℝ-Vector-Space =
    let
      dist-V = dist-Normed-ℝ-Vector-Space V
      norm-V = map-norm-Normed-ℝ-Vector-Space V
      _*V_ = mul-Normed-ℝ-Vector-Space V
      _-V_ = diff-Normed-ℝ-Vector-Space V
    in
      is-lipschitz-real-constant-map-Normed-ℝ-Vector-Space
        ( normed-real-vector-space-ℝ l1)
        ( V)
        ( λ c → mul-Normed-ℝ-Vector-Space V c v)
        ( nonnegative-norm-Normed-ℝ-Vector-Space V v)
        ( λ c1 c2 →
          leq-eq-ℝ
            ( equational-reasoning
              dist-V (c1 *V v) (c2 *V v)
              ＝ norm-V ((c1 -ℝ c2) *V v)
                by
                  ap
                    ( norm-V)
                    ( inv
                      ( right-distributive-mul-diff-Normed-ℝ-Vector-Space V
                        ( c1)
                        ( c2)
                        ( v)))
              ＝ dist-ℝ c1 c2 *ℝ norm-V v
                by is-absolutely-homogeneous-norm-Normed-ℝ-Vector-Space V _ _
              ＝ norm-V v *ℝ dist-ℝ c1 c2
                by commutative-mul-ℝ _ _))
```
