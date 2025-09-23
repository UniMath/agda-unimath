# Convolution of sequences in commutative semirings

```agda
module commutative-algebra.convolution-sequences-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.function-commutative-semirings
open import commutative-algebra.sums-of-finite-families-of-elements-commutative-semirings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-semirings

open import elementary-number-theory.binary-sum-decompositions-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.semigroups

open import lists.sequences

open import ring-theory.semirings

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "convolution" WD="convolution" Disambiguation="of sequences in commutative semirings" Agda=convolution-sequence-Commutative-Semiring WDID=Q210857}}
of two [sequences](lists.sequences.md) `aₙ` and `bₙ` of elements in a
[commutative semiring](commutative-algebra.commutative-semirings.md) is the new
sequence

```text
  cₙ = ∑_{0 ≤ i ≤ n} aₙ bₙ₋ᵢ
```

With pairwise addition, this operation forms a new commutative semiring.

## Definition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  convolution-sequence-Commutative-Semiring :
    sequence (type-Commutative-Semiring R) →
    sequence (type-Commutative-Semiring R) →
    sequence (type-Commutative-Semiring R)
  convolution-sequence-Commutative-Semiring a b n =
    sum-finite-Commutative-Semiring
      ( R)
      ( finite-type-binary-sum-decomposition-ℕ n)
      ( λ (i , j , j+i=n) → mul-Commutative-Semiring R (a i) (b j))
```

## Properties

### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  abstract
    htpy-commutative-convolution-sequence-Commutative-Semiring :
      (a b : sequence (type-Commutative-Semiring R)) →
      convolution-sequence-Commutative-Semiring R a b ~
      convolution-sequence-Commutative-Semiring R b a
    htpy-commutative-convolution-sequence-Commutative-Semiring a b n =
      equational-reasoning
        sum-finite-Commutative-Semiring
          ( R)
          ( finite-type-binary-sum-decomposition-ℕ n)
          ( λ (i , j , j+i=n) → mul-Commutative-Semiring R (a i) (b j))
        ＝
          sum-finite-Commutative-Semiring
            ( R)
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ (i , j , j+i=n) → mul-Commutative-Semiring R (a j) (b i))
          by
            sum-aut-finite-Commutative-Semiring
              ( R)
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( aut-swap-binary-sum-decomposition-ℕ n)
              ( _)
        ＝
          sum-finite-Commutative-Semiring
            ( R)
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ (i , j , j+i=n) → mul-Commutative-Semiring R (b i) (a j))
          by
            htpy-sum-finite-Commutative-Semiring R _
              ( λ (i , j , j+i=n) → commutative-mul-Commutative-Semiring R _ _)

  commutative-convolution-sequence-Commutative-Semiring :
    (a b : sequence (type-Commutative-Semiring R)) →
    convolution-sequence-Commutative-Semiring R a b ＝
    convolution-sequence-Commutative-Semiring R b a
  commutative-convolution-sequence-Commutative-Semiring a b =
    eq-htpy (htpy-commutative-convolution-sequence-Commutative-Semiring a b)
```

### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  unit-convolution-sequence-Commutative-Semiring :
    sequence (type-Commutative-Semiring R)
  unit-convolution-sequence-Commutative-Semiring zero-ℕ =
    one-Commutative-Semiring R
  unit-convolution-sequence-Commutative-Semiring (succ-ℕ n) =
    zero-Commutative-Semiring R

  abstract
    htpy-left-unit-law-convolution-sequence-Commutative-Semiring :
      (a : sequence (type-Commutative-Semiring R)) →
      convolution-sequence-Commutative-Semiring R
        ( unit-convolution-sequence-Commutative-Semiring)
        ( a) ~
      a
    htpy-left-unit-law-convolution-sequence-Commutative-Semiring a n =
      equational-reasoning
        sum-finite-Commutative-Semiring R
          ( finite-type-binary-sum-decomposition-ℕ n)
          ( λ (i , j , j+i=n) →
            mul-Commutative-Semiring R
              ( unit-convolution-sequence-Commutative-Semiring i)
              ( a j))
        ＝
          add-Commutative-Semiring R
            ( sum-fin-sequence-type-Commutative-Semiring R
              ( n)
              ( λ k →
                mul-Commutative-Semiring R (zero-Commutative-Semiring R) _))
            ( mul-Commutative-Semiring R (one-Commutative-Semiring R) (a n))
            by
              eq-sum-finite-sum-count-Commutative-Semiring R
                ( finite-type-binary-sum-decomposition-ℕ n)
                ( count-reverse-binary-sum-decomposition-ℕ n)
                ( _)
        ＝
          add-Commutative-Semiring R
            ( sum-fin-sequence-type-Commutative-Semiring R
              ( n)
              ( λ _ → zero-Commutative-Semiring R))
            ( a n)
            by
              ap-add-Commutative-Semiring R
                ( htpy-sum-fin-sequence-type-Commutative-Semiring R n
                  ( λ _ → left-zero-law-mul-Commutative-Semiring R _))
                ( left-unit-law-mul-Commutative-Semiring R _)
        ＝
          add-Commutative-Semiring R
            ( zero-Commutative-Semiring R)
            ( a n)
            by
              ap-add-Commutative-Semiring R
                ( sum-zero-fin-sequence-type-Commutative-Semiring R n)
                ( refl)
        ＝ a n by left-unit-law-add-Commutative-Semiring R _

  left-unit-law-convolution-sequence-Commutative-Semiring :
    (a : sequence (type-Commutative-Semiring R)) →
    convolution-sequence-Commutative-Semiring R
      ( unit-convolution-sequence-Commutative-Semiring)
      ( a) ＝
    a
  left-unit-law-convolution-sequence-Commutative-Semiring a =
    eq-htpy (htpy-left-unit-law-convolution-sequence-Commutative-Semiring a)

  right-unit-law-convolution-sequence-Commutative-Semiring :
    (a : sequence (type-Commutative-Semiring R)) →
    convolution-sequence-Commutative-Semiring R
      ( a)
      ( unit-convolution-sequence-Commutative-Semiring) ＝
    a
  right-unit-law-convolution-sequence-Commutative-Semiring a =
    commutative-convolution-sequence-Commutative-Semiring R _ _ ∙
    left-unit-law-convolution-sequence-Commutative-Semiring a
```

### Associativity

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  abstract
    htpy-associative-convolution-sequence-Commutative-Semiring :
      (a b c : sequence (type-Commutative-Semiring R)) →
      convolution-sequence-Commutative-Semiring R
        ( convolution-sequence-Commutative-Semiring R a b)
        ( c) ~
      convolution-sequence-Commutative-Semiring R
        ( a)
        ( convolution-sequence-Commutative-Semiring R b c)
    htpy-associative-convolution-sequence-Commutative-Semiring a b c n =
      let
        _*R_ :
          type-Commutative-Semiring R → type-Commutative-Semiring R →
          type-Commutative-Semiring R
        _*R_ = mul-Commutative-Semiring R
      in equational-reasoning
        sum-finite-Commutative-Semiring
          ( R)
          ( finite-type-binary-sum-decomposition-ℕ n)
          ( λ (i , j , _) →
            ( sum-finite-Commutative-Semiring
              ( R)
              ( finite-type-binary-sum-decomposition-ℕ i)
              ( λ (k , l , _) → a k *R b l)) *R
            c j)
        ＝
          sum-finite-Commutative-Semiring
            ( R)
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ (i , j , _) →
              ( sum-finite-Commutative-Semiring
                ( R)
                ( finite-type-binary-sum-decomposition-ℕ i)
                ( λ (k , l , _) → (a k *R b l) *R c j)))
          by
            htpy-sum-finite-Commutative-Semiring R _
              ( λ (i , j , _) →
                right-distributive-mul-sum-finite-Commutative-Semiring R _ _
                  ( c j))
        ＝
          sum-finite-Commutative-Semiring
            ( R)
            ( Σ-Finite-Type
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ i))
            ( λ ((i , j , _) , k , l , _) → (a k *R b l) *R c j)
          by
            inv
              ( sum-Σ-finite-Commutative-Semiring
                ( R)
                ( finite-type-binary-sum-decomposition-ℕ n)
                ( λ (i , _ , _) → finite-type-binary-sum-decomposition-ℕ i)
                ( _))
        ＝
          sum-finite-Commutative-Semiring
              ( R)
              ( Σ-Finite-Type
                ( finite-type-binary-sum-decomposition-ℕ n)
                ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ j))
              ( λ ((i , j , _) , k , l , _) → (a k *R b l) *R c i)
          by
            sum-equiv-finite-Commutative-Semiring R _ _
              ( equiv-binary-sum-decomposition-pr1-pr2 n)
              ( _)
        ＝
          sum-finite-Commutative-Semiring
            ( R)
            ( Σ-Finite-Type
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ j))
            ( λ ((i , j , _) , k , l , _) → a k *R (b l *R c i))
          by
            htpy-sum-finite-Commutative-Semiring R _
              ( λ ((i , j , _) , k , l , _) →
                associative-mul-Commutative-Semiring R _ _ _)
        ＝
          sum-finite-Commutative-Semiring
            ( R)
            ( Σ-Finite-Type
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ j))
            ( λ ((i , j , _) , k , l , _) → a i *R (b k *R c l))
          by
            sum-aut-finite-Commutative-Semiring
              ( R)
              ( Σ-Finite-Type
                ( finite-type-binary-sum-decomposition-ℕ n)
                ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ j))
              ( equiv-permute-components-triple-with-sum-pr2 n)
              ( _)
        ＝
          sum-finite-Commutative-Semiring
            ( R)
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ (i , j , _) →
              sum-finite-Commutative-Semiring
                ( R)
                ( finite-type-binary-sum-decomposition-ℕ j)
                ( λ (k , l , _) → a i *R (b k *R c l)))
          by
            sum-Σ-finite-Commutative-Semiring
              ( R)
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ j)
              ( _)
        ＝
          sum-finite-Commutative-Semiring
            ( R)
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ (i , j , _) →
              a i *R
              sum-finite-Commutative-Semiring
                ( R)
                ( finite-type-binary-sum-decomposition-ℕ j)
                ( λ (k , l , _) → b k *R c l))
          by
            htpy-sum-finite-Commutative-Semiring R _
              ( λ (i , j , _) →
                inv
                  ( left-distributive-mul-sum-finite-Commutative-Semiring
                    ( R)
                    ( _)
                    ( _)
                    ( _)))

  associative-convolution-sequence-Commutative-Semiring :
    (a b c : sequence (type-Commutative-Semiring R)) →
    convolution-sequence-Commutative-Semiring R
      ( convolution-sequence-Commutative-Semiring R a b)
      ( c) ＝
    convolution-sequence-Commutative-Semiring R
      ( a)
      ( convolution-sequence-Commutative-Semiring R b c)
  associative-convolution-sequence-Commutative-Semiring a b c =
    eq-htpy (htpy-associative-convolution-sequence-Commutative-Semiring a b c)
```

### Zero laws

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  abstract
    htpy-left-zero-law-convolution-sequence-Commutative-Semiring :
      (a : sequence (type-Commutative-Semiring R)) →
      convolution-sequence-Commutative-Semiring R
        ( zero-function-Commutative-Semiring R ℕ)
        ( a) ~
      zero-function-Commutative-Semiring R ℕ
    htpy-left-zero-law-convolution-sequence-Commutative-Semiring a n =
      htpy-sum-finite-Commutative-Semiring R _
        (λ (i , j , _) → left-zero-law-mul-Commutative-Semiring R _) ∙
      sum-zero-finite-Commutative-Semiring R _

    left-zero-law-convolution-sequence-Commutative-Semiring :
      (a : sequence (type-Commutative-Semiring R)) →
      convolution-sequence-Commutative-Semiring R
        ( zero-function-Commutative-Semiring R ℕ)
        ( a) ＝
      zero-function-Commutative-Semiring R ℕ
    left-zero-law-convolution-sequence-Commutative-Semiring a =
      eq-htpy (htpy-left-zero-law-convolution-sequence-Commutative-Semiring a)

    right-zero-law-convolution-sequence-Commutative-Semiring :
      (a : sequence (type-Commutative-Semiring R)) →
      convolution-sequence-Commutative-Semiring R
        ( a)
        ( zero-function-Commutative-Semiring R ℕ) ＝
      zero-function-Commutative-Semiring R ℕ
    right-zero-law-convolution-sequence-Commutative-Semiring a =
      commutative-convolution-sequence-Commutative-Semiring R _ _ ∙
      left-zero-law-convolution-sequence-Commutative-Semiring a
```

### Distributivity laws

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  abstract
    htpy-left-distributive-convolution-add-sequence-Commutative-Semiring :
      (a b c : sequence (type-Commutative-Semiring R)) →
      convolution-sequence-Commutative-Semiring R
        ( a)
        ( add-function-Commutative-Semiring R ℕ b c) ~
      add-function-Commutative-Semiring R ℕ
        ( convolution-sequence-Commutative-Semiring R a b)
        ( convolution-sequence-Commutative-Semiring R a c)
    htpy-left-distributive-convolution-add-sequence-Commutative-Semiring
      a b c n =
        htpy-sum-finite-Commutative-Semiring R _
          ( λ _ → left-distributive-mul-add-Commutative-Semiring R _ _ _) ∙
        interchange-sum-add-finite-Commutative-Semiring R _ _ _

    left-distributive-convolution-add-sequence-Commutative-Semiring :
      (a b c : sequence (type-Commutative-Semiring R)) →
      convolution-sequence-Commutative-Semiring R
        ( a)
        ( add-function-Commutative-Semiring R ℕ b c) ＝
      add-function-Commutative-Semiring R ℕ
        ( convolution-sequence-Commutative-Semiring R a b)
        ( convolution-sequence-Commutative-Semiring R a c)
    left-distributive-convolution-add-sequence-Commutative-Semiring a b c =
      eq-htpy
        ( htpy-left-distributive-convolution-add-sequence-Commutative-Semiring
          ( a)
          ( b)
          ( c))

    right-distributive-convolution-add-sequence-Commutative-Semiring :
      (a b c : sequence (type-Commutative-Semiring R)) →
      convolution-sequence-Commutative-Semiring R
        ( add-function-Commutative-Semiring R ℕ a b)
        ( c) ＝
      add-function-Commutative-Semiring R ℕ
        ( convolution-sequence-Commutative-Semiring R a c)
        ( convolution-sequence-Commutative-Semiring R b c)
    right-distributive-convolution-add-sequence-Commutative-Semiring a b c =
      equational-reasoning
        convolution-sequence-Commutative-Semiring R
          ( add-function-Commutative-Semiring R ℕ a b)
          ( c)
        ＝
          convolution-sequence-Commutative-Semiring R
            ( c)
            ( add-function-Commutative-Semiring R ℕ a b)
          by commutative-convolution-sequence-Commutative-Semiring R _ _
        ＝
          add-function-Commutative-Semiring R ℕ
            ( convolution-sequence-Commutative-Semiring R c a)
            ( convolution-sequence-Commutative-Semiring R c b)
          by
            left-distributive-convolution-add-sequence-Commutative-Semiring
              ( c)
              ( a)
              ( b)
        ＝
          add-function-Commutative-Semiring R ℕ
            ( convolution-sequence-Commutative-Semiring R a c)
            ( convolution-sequence-Commutative-Semiring R b c)
          by
            ap-binary
              ( add-function-Commutative-Semiring R ℕ)
              ( commutative-convolution-sequence-Commutative-Semiring R c a)
              ( commutative-convolution-sequence-Commutative-Semiring R c b)
```

### Commutative semiring of sequences of elements of commutative semirings under convolution

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  additive-commutative-monoid-sequence-Commutative-Semiring :
    Commutative-Monoid l
  additive-commutative-monoid-sequence-Commutative-Semiring =
    additive-commutative-monoid-function-Commutative-Semiring R ℕ

  has-associative-mul-convolution-sequence-Commutative-Semiring :
    has-associative-mul (sequence (type-Commutative-Semiring R))
  pr1 has-associative-mul-convolution-sequence-Commutative-Semiring =
    convolution-sequence-Commutative-Semiring R
  pr2 has-associative-mul-convolution-sequence-Commutative-Semiring =
    associative-convolution-sequence-Commutative-Semiring R

  is-unital-convolution-sequence-Commutative-Semiring :
    is-unital (convolution-sequence-Commutative-Semiring R)
  pr1 is-unital-convolution-sequence-Commutative-Semiring =
    unit-convolution-sequence-Commutative-Semiring R
  pr1 (pr2 is-unital-convolution-sequence-Commutative-Semiring) =
    left-unit-law-convolution-sequence-Commutative-Semiring R
  pr2 (pr2 is-unital-convolution-sequence-Commutative-Semiring) =
    right-unit-law-convolution-sequence-Commutative-Semiring R

  has-mul-convolution-additive-commutative-monoid-sequence-Commutative-Semiring :
    has-mul-Commutative-Monoid
      additive-commutative-monoid-sequence-Commutative-Semiring
  has-mul-convolution-additive-commutative-monoid-sequence-Commutative-Semiring =
    ( has-associative-mul-convolution-sequence-Commutative-Semiring ,
      is-unital-convolution-sequence-Commutative-Semiring ,
      left-distributive-convolution-add-sequence-Commutative-Semiring R ,
      right-distributive-convolution-add-sequence-Commutative-Semiring R)

  zero-laws-convolution-additive-commutative-monoid-sequence-Commutative-Semiring :
    zero-laws-Commutative-Monoid
      ( additive-commutative-monoid-sequence-Commutative-Semiring)
      ( has-mul-convolution-additive-commutative-monoid-sequence-Commutative-Semiring)
  pr1
    zero-laws-convolution-additive-commutative-monoid-sequence-Commutative-Semiring =
    left-zero-law-convolution-sequence-Commutative-Semiring R
  pr2
    zero-laws-convolution-additive-commutative-monoid-sequence-Commutative-Semiring =
    right-zero-law-convolution-sequence-Commutative-Semiring R

  semiring-convolution-sequence-Commutative-Semiring : Semiring l
  pr1 semiring-convolution-sequence-Commutative-Semiring =
    additive-commutative-monoid-sequence-Commutative-Semiring
  pr1 (pr2 semiring-convolution-sequence-Commutative-Semiring) =
    has-mul-convolution-additive-commutative-monoid-sequence-Commutative-Semiring
  pr2 (pr2 semiring-convolution-sequence-Commutative-Semiring) =
    zero-laws-convolution-additive-commutative-monoid-sequence-Commutative-Semiring

  commutative-semiring-convolution-sequence-Commutative-Semiring :
    Commutative-Semiring l
  pr1 commutative-semiring-convolution-sequence-Commutative-Semiring =
    semiring-convolution-sequence-Commutative-Semiring
  pr2 commutative-semiring-convolution-sequence-Commutative-Semiring =
    commutative-convolution-sequence-Commutative-Semiring R
```
