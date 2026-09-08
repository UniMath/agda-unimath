# Permutation matrices on rings

```agda
module linear-algebra.permutation-matrices-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.identity-matrices-on-rings
open import linear-algebra.indicator-finite-sequences-in-rings
open import linear-algebra.matrices-on-rings
open import linear-algebra.multiplication-matrices-on-rings
open import linear-algebra.multiplication-square-matrices-on-rings
open import linear-algebra.permutation-of-matrices
open import linear-algebra.square-matrices-on-rings
open import linear-algebra.transposition-matrices

open import ring-theory.rings
open import ring-theory.sums-of-finite-sequences-of-elements-rings

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "permutation matrix" WDID=Q851512 WD="permutation matrix" Disambiguation="in a ring" Agda=permutation-matrix-Ring}}
of a [permutation](finite-group-theory.permutations-standard-finite-types.md)
`σ` of `Fin n` in a [ring](ring-theory.rings.md) is the `n × n`
[square matrix](linear-algebra.square-matrices-on-rings.md) `M` where `Mᵢⱼ` is
`1` if `j = σ(i)` and `0` otherwise.

## Definition

```agda
permutation-matrix-Ring :
  {l : Level} (R : Ring l) (n : ℕ) → Permutation n → square-matrix-Ring R n
permutation-matrix-Ring R n σ i =
  indicator-fin-sequence-type-Ring R n (map-equiv σ i)
```

## Properties

### The permutation matrix of the identity permutation is the identity matrix

```agda
id-permutation-matrix-Ring :
  {l : Level} (R : Ring l) (n : ℕ) →
  permutation-matrix-Ring R n id-equiv ＝ id-matrix-Ring R n
id-permutation-matrix-Ring R n = refl
```

### The transpose of the matrix of a permutation `σ` is the matrix of the permutation `σ⁻¹`

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  (σ : Permutation n)
  where abstract

  binary-htpy-transpose-permutation-matrix-Ring :
    binary-htpy
      ( transpose-square-matrix n (permutation-matrix-Ring R n σ))
      ( permutation-matrix-Ring R n (inv-equiv σ))
  binary-htpy-transpose-permutation-matrix-Ring i j =
    let
      is-prop-is-decidable-σj=i =
        is-prop-is-decidable (is-set-Fin n (map-equiv σ j) i)
      is-prop-is-decidable-σ⁻¹i=j =
        is-prop-is-decidable (is-set-Fin n (map-inv-equiv σ i) j)
      σj=i⇒σ⁻¹i=j σj=i =
        ap (map-inv-equiv σ) (inv σj=i) ∙ is-retraction-map-inv-equiv σ j
    in
      rec-coproduct
        ( λ σj=i →
          equational-reasoning
            rec-coproduct
              ( λ _ → one-Ring R)
              ( λ _ → zero-Ring R)
              ( has-decidable-equality-Fin n (map-equiv σ j) i)
            ＝ one-Ring R
              by
                ap
                  ( rec-coproduct _ _)
                  ( eq-is-prop'
                    ( is-prop-is-decidable (is-set-Fin n (map-equiv σ j) i))
                    ( has-decidable-equality-Fin n (map-equiv σ j) i)
                    ( inl σj=i))
            ＝
              rec-coproduct
                ( λ _ → one-Ring R)
                ( λ _ → zero-Ring R)
                ( has-decidable-equality-Fin n (map-inv-equiv σ i) j)
              by
                ap
                  ( rec-coproduct _ _)
                  ( eq-is-prop'
                    ( is-prop-is-decidable (is-set-Fin n (map-inv-equiv σ i) j))
                    ( inl (σj=i⇒σ⁻¹i=j σj=i))
                    ( has-decidable-equality-Fin n (map-inv-equiv σ i) j)))
        ( λ σj≠i →
          equational-reasoning
            rec-coproduct
              ( λ _ → one-Ring R)
              ( λ _ → zero-Ring R)
              ( has-decidable-equality-Fin n (map-equiv σ j) i)
            ＝ zero-Ring R
              by
                ap
                  ( rec-coproduct _ _)
                  ( eq-is-prop'
                    ( is-prop-is-decidable (is-set-Fin n (map-equiv σ j) i))
                    ( has-decidable-equality-Fin n (map-equiv σ j) i)
                    ( inr σj≠i))
            ＝
              rec-coproduct
                ( λ _ → one-Ring R)
                ( λ _ → zero-Ring R)
                ( has-decidable-equality-Fin n (map-inv-equiv σ i) j)
              by
                ap
                  ( rec-coproduct _ _)
                  ( eq-is-prop'
                    ( is-prop-is-decidable (is-set-Fin n (map-inv-equiv σ i) j))
                    ( inr (map-neg (eq-map-equiv-eq-map-inv-equiv σ j i) σj≠i))
                    ( has-decidable-equality-Fin n (map-inv-equiv σ i) j)))
        ( has-decidable-equality-Fin n (map-equiv σ j) i)

  transpose-permutation-matrix-Ring :
    transpose-square-matrix n (permutation-matrix-Ring R n σ) ＝
    permutation-matrix-Ring R n (inv-equiv σ)
  transpose-permutation-matrix-Ring =
    eq-binary-htpy _ _ binary-htpy-transpose-permutation-matrix-Ring
```

### Left multiplication by a permutation matrix permutes the rows of a matrix

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n : ℕ)
  (σ : Permutation m)
  (M : matrix-Ring R m n)
  where abstract

  binary-htpy-left-mul-permutation-matrix-Ring :
    binary-htpy
      ( mul-matrix-Ring R m m n (permutation-matrix-Ring R m σ) M)
      ( permute-rows-matrix m n σ M)
  binary-htpy-left-mul-permutation-matrix-Ring i j =
    left-dot-product-indicator-fin-sequence-type-Ring
      ( R)
      ( m)
      ( map-equiv σ i)
      ( transpose-matrix m n M j)

  left-mul-permutation-matrix-Ring :
    mul-matrix-Ring R m m n (permutation-matrix-Ring R m σ) M ＝
    ( permute-rows-matrix m n σ M)
  left-mul-permutation-matrix-Ring =
    eq-binary-htpy _ _ binary-htpy-left-mul-permutation-matrix-Ring
```

### Right multiplication by a matrix for the permutation `σ` permutes the columns of a matrix by `σ⁻¹`

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n : ℕ)
  (σ : Permutation n)
  (M : matrix-Ring R m n)
  where abstract

  binary-htpy-right-mul-permutation-matrix-Ring :
    binary-htpy
      ( mul-matrix-Ring R m n n M (permutation-matrix-Ring R n σ))
      ( permute-columns-matrix m n (inv-equiv σ) M)
  binary-htpy-right-mul-permutation-matrix-Ring i j =
    equational-reasoning
      sum-fin-sequence-type-Ring R n
        ( λ k → mul-Ring R (M i k) (permutation-matrix-Ring R n σ k j))
      ＝
        sum-fin-sequence-type-Ring R n
          ( λ k →
            mul-Ring R
              ( M i k)
              ( permutation-matrix-Ring R n (inv-equiv σ) j k))
        by
          htpy-sum-fin-sequence-type-Ring R n
            ( λ k →
              ap-mul-Ring R
                ( refl)
                ( binary-htpy-transpose-permutation-matrix-Ring R n σ j k))
      ＝ M i (map-inv-equiv σ j)
        by
          right-dot-product-indicator-fin-sequence-type-Ring R
            ( n)
            ( map-inv-equiv σ j)
            ( M i)

  right-mul-permutation-matrix-Ring :
    mul-matrix-Ring R m n n M (permutation-matrix-Ring R n σ) ＝
    permute-columns-matrix m n (inv-equiv σ) M
  right-mul-permutation-matrix-Ring =
    eq-binary-htpy _ _ binary-htpy-right-mul-permutation-matrix-Ring
```
