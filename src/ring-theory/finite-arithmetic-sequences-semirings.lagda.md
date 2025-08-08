# Finite arithmetic sequences in semirings

```agda
module ring-theory.finite-arithmetic-sequences-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binary-sum-decompositions-natural-numbers
open import elementary-number-theory.commutative-semiring-of-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.powers-of-elements-commutative-monoids

open import lists.finite-sequences

open import ring-theory.semirings
open import ring-theory.sums-of-finite-families-of-elements-semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A {{#concept "finite arithmetic sequence" disambiguation="in a semiring"}} in a
[semiring](ring-theory.semirings.md) `R` with length `n : ℕ`, initial term
`a : R`, and common difference `d : R`, is a
[finite sequence](lists.finite-sequences.md) mapping `i < n` to `a + i * d`,
where `i` is interpreted as the image in `R` of `i` under the
[initial homomorphism of semirings](elementary-number-theory.commutative-semiring-of-natural-numbers.md)
from `ℕ` to `R`.

## Definition

```agda
fin-arithmetic-sequence-Semiring :
  {l : Level} (R : Semiring l)
  (n : ℕ) (a d : type-Semiring R) →
  fin-sequence (type-Semiring R) n
fin-arithmetic-sequence-Semiring R n a d i =
  add-Semiring R
    ( a)
    ( mul-Semiring R
      ( map-initial-hom-Semiring R (nat-Fin n i))
      ( d))
```

## Properties

### Formula for the sum of an arithmetic sequence

```agda
module _
  {l : Level} (R : Semiring l)
  (n : ℕ) (a d : type-Semiring R)
  where

  sum-arithmetic-sequence-Semiring :
    mul-Semiring R
      ( map-initial-hom-Semiring R 2)
      ( sum-fin-sequence-type-Semiring
        ( R)
        ( succ-ℕ n)
        ( fin-arithmetic-sequence-Semiring R (succ-ℕ n) a d)) ＝
    mul-Semiring R
      ( map-initial-hom-Semiring R (succ-ℕ n))
      ( add-Semiring R
        ( a)
        ( add-Semiring R
          ( a)
          ( mul-Semiring R
            ( map-initial-hom-Semiring R n)
            ( d))))
  sum-arithmetic-sequence-Semiring =
    equational-reasoning
      mul-Semiring R
        ( map-initial-hom-Semiring R 2)
        ( sum-fin-sequence-type-Semiring R
          ( succ-ℕ n)
          ( fin-arithmetic-sequence-Semiring R (succ-ℕ n) a d))
      ＝
        mul-Semiring R
          ( map-initial-hom-Semiring R 2)
          ( sum-finite-Semiring R
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ ( i , j , j+i=n) →
              add-Semiring R
                ( a)
                ( mul-Semiring R (map-initial-hom-Semiring R i) d)))
        by
          ap
            ( mul-Semiring R _)
            ( inv
              ( eq-sum-finite-sum-count-Semiring R
                ( _)
                ( count-binary-sum-decomposition-ℕ _)
                ( _)))
      ＝
        add-Semiring R
          ( sum-finite-Semiring R
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ ( i , j , j+i=n) →
              add-Semiring R
                ( a)
                ( mul-Semiring R (map-initial-hom-Semiring R i) d)))
          ( sum-finite-Semiring R
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ ( i , j , j+i=n) →
              add-Semiring R
                ( a)
                ( mul-Semiring R (map-initial-hom-Semiring R i) d)))
        by left-mul-initial-hom-Semiring R 2 _
      ＝
        add-Semiring R
          ( sum-finite-Semiring R
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ ( i , j , j+i=n) →
              add-Semiring R
                ( a)
                ( mul-Semiring R (map-initial-hom-Semiring R i) d)))
          ( sum-finite-Semiring R
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ ( i , j , j+i=n) →
              add-Semiring R
                ( a)
                ( mul-Semiring R (map-initial-hom-Semiring R j) d)))
        by
          ap-add-Semiring R
            ( refl)
            ( sum-aut-finite-Semiring R
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( aut-swap-binary-sum-decomposition-ℕ n)
              ( _))
      ＝
        sum-finite-Semiring R
          ( finite-type-binary-sum-decomposition-ℕ n)
          ( λ ( i , j , j+i=n) →
            add-Semiring R
              ( add-Semiring R
                ( a)
                ( mul-Semiring R (map-initial-hom-Semiring R i) d))
              ( add-Semiring R
                ( a)
                ( mul-Semiring R (map-initial-hom-Semiring R j) d)))
        by inv (interchange-sum-add-finite-Semiring R _ _ _)
      ＝
        sum-finite-Semiring R
          ( finite-type-binary-sum-decomposition-ℕ n)
          ( λ ( i , j , j+i=n) →
            add-Semiring R
              ( a)
              ( add-Semiring R
                ( a)
                ( mul-Semiring R (map-initial-hom-Semiring R n) d)))
        by
          htpy-sum-finite-Semiring R _
            ( λ (i , j , j+i=n) →
              equational-reasoning
                add-Semiring R
                  ( add-Semiring R
                    ( a)
                    ( mul-Semiring R (map-initial-hom-Semiring R i) d))
                  ( add-Semiring R
                    ( a)
                    ( mul-Semiring R (map-initial-hom-Semiring R j) d))
                ＝
                  add-Semiring R
                    ( add-Semiring R
                      ( a)
                      ( a))
                    ( add-Semiring R
                      ( mul-Semiring R (map-initial-hom-Semiring R i) d)
                      ( mul-Semiring R (map-initial-hom-Semiring R j) d))
                  by interchange-add-add-Semiring R _ _ _ _
                ＝
                  add-Semiring R
                    ( add-Semiring R
                      ( a)
                      ( a))
                    ( mul-Semiring R
                      ( add-Semiring R
                        ( map-initial-hom-Semiring R i)
                        ( map-initial-hom-Semiring R j))
                      ( d))
                  by
                    ap-add-Semiring R
                      ( refl)
                      ( inv (right-distributive-mul-add-Semiring R _ _ _))
                ＝
                  add-Semiring R
                    ( add-Semiring R
                      ( a)
                      ( a))
                    ( mul-Semiring R
                      ( map-initial-hom-Semiring R (i +ℕ j))
                      ( d))
                  by
                    ap-add-Semiring R
                      ( refl)
                      ( ap-mul-Semiring R
                        ( inv (preserves-add-initial-hom-Semiring R i j))
                        ( refl))
                ＝
                  add-Semiring R
                    ( add-Semiring R
                      ( a)
                      ( a))
                    ( mul-Semiring R
                      ( map-initial-hom-Semiring R n)
                      ( d))
                  by
                    ap
                      ( λ m →
                        add-Semiring R
                          ( _)
                          ( mul-Semiring R (map-initial-hom-Semiring R m) d))
                      ( commutative-add-ℕ i j ∙ j+i=n)
                ＝
                  add-Semiring R
                    ( a)
                    ( add-Semiring R
                      ( a)
                      ( mul-Semiring R
                        ( map-initial-hom-Semiring R n)
                        ( d)))
                  by associative-add-Semiring R _ _ _)
      ＝
        power-Commutative-Monoid
          ( additive-commutative-monoid-Semiring R)
          ( number-of-elements-Finite-Type
            ( finite-type-binary-sum-decomposition-ℕ n))
          ( add-Semiring R
            ( a)
            ( add-Semiring R
              ( a)
              ( mul-Semiring R
                ( map-initial-hom-Semiring R n)
                ( d))))
        by sum-const-finite-type-Semiring R _ _
      ＝
        power-Commutative-Monoid
          ( additive-commutative-monoid-Semiring R)
          ( succ-ℕ n)
          ( add-Semiring R
            ( a)
            ( add-Semiring R
              ( a)
              ( mul-Semiring R
                ( map-initial-hom-Semiring R n)
                ( d))))
        by
          ap
            ( λ m →
              power-Commutative-Monoid
                ( additive-commutative-monoid-Semiring R)
                ( m)
                ( add-Semiring R
                  ( a)
                  ( add-Semiring R
                    ( a)
                    ( mul-Semiring R
                      ( map-initial-hom-Semiring R n)
                      ( d)))))
            ( number-of-elements-finite-type-binary-sum-decomposition-ℕ n)
      ＝
        mul-Semiring
          ( R)
          ( map-initial-hom-Semiring R (succ-ℕ n))
          ( add-Semiring R
            ( a)
            ( add-Semiring R
              ( a)
              ( mul-Semiring R
                ( map-initial-hom-Semiring R n)
                ( d))))
        by inv (left-mul-initial-hom-Semiring R (succ-ℕ n) _)
```
