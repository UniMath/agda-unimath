# Determinants of square matrices on commutative rings

```agda
module linear-algebra.determinants-square-matrices-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.products-of-finite-sequences-of-elements-commutative-rings
open import commutative-algebra.sums-of-finite-families-of-elements-commutative-rings

open import elementary-number-theory.natural-numbers

open import finite-group-theory.counting-permutations-standard-finite-types
open import finite-group-theory.permutations
open import finite-group-theory.sign-homomorphism

open import foundation.coproduct-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.universe-levels

open import linear-algebra.square-matrices-on-commutative-rings

open import univalent-combinatorics.finite-types
```

</details>

## Idea

The
{{#concept "determinant" WDID=Q178546 WD="determinant" Disambiguation="of a square matrix on a commutative ring" Agda=determinant-square-matrix-Commutative-Ring}}
of an `n × n`
[square matrix](linear-algebra.square-matrices-on-commutative-rings.md) `M` on a
[commutative ring](commutative-algebra.commutative-rings.md) `R` is the sum over
all [permutations](finite-group-theory.permutations.md) `σ` of the
[standard finite type](univalent-combinatorics.standard-finite-types.md) with
`n` elements `∑ sgn(σ) ∏ᵢ M(i , σ(i))`.

## Definition

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  where

  opaque
    determinant-square-matrix-Commutative-Ring :
      square-matrix-Commutative-Ring R n →
      type-Commutative-Ring R
    determinant-square-matrix-Commutative-Ring M =
      sum-finite-Commutative-Ring
        ( R)
        ( finite-type-Permutation n)
        ( λ σ →
          rec-coproduct
            ( λ _ → id)
            ( λ _ → neg-Commutative-Ring R)
            ( sign-homomorphism-Fin-2
              ( n)
              ( Fin-Type-With-Cardinality-ℕ n)
              ( σ))
            ( product-fin-sequence-type-Commutative-Ring
              ( R)
              ( n)
              ( λ i → M i (map-equiv σ i))))
```

## External links

- [Determinant](https://en.wikipedia.org/wiki/Determinant) on Wikipedia
