# Convolution of sequences in semirings

```agda
module ring-theory.convolution-sequences-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.binary-sum-decompositions-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.commuting-elements-monoids
open import group-theory.semigroups

open import lists.sequences

open import ring-theory.dirac-sequences-semirings
open import ring-theory.semirings
open import ring-theory.sequences-semirings
open import ring-theory.sums-of-finite-families-of-elements-semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings

open import univalent-combinatorics.dependent-pair-types
```

</details>

## Idea

The
{{#concept "convolution product" WD="convolution" Disambiguation="of sequences in semirings" Agda=mul-convolution-sequence-Semiring WDID=Q210857}}
of two [sequences](ring-theory.sequences-semirings.md) `aₙ` and `bₙ` in a
[semiring](ring-theory.semirings.md) is the sequence `c = a ⋆ b` defined by:

```text
  cₙ = ∑_{0 ≤ i ≤ n} aₙ bₙ₋ᵢ
```

With pairwise addition, this operation forms the
{{#concept "convolution semiring" Disambiguation="of sequences in a semiring" Agda=convolution-sequence-Semiring}}
of sequences in a semiring.

Unlike the pointwise semiring structure, the unit of the **convolution
semiring** is the [dirac sequence](ring-theory.dirac-sequences-semirings.md) at
`0`, `δ₀ : ℕ → R` given by `(1, 0, 0, 0, ...)`.

## Definitions

### The convolution product of sequences in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  mul-convolution-sequence-Semiring :
    type-sequence-Semiring R →
    type-sequence-Semiring R →
    type-sequence-Semiring R
  mul-convolution-sequence-Semiring a b n =
    sum-finite-Semiring
      ( R)
      ( finite-type-binary-sum-decomposition-ℕ n)
      ( λ (i , j , j+i=n) → mul-Semiring R (a i) (b j))
```

### The unit of the convolution product

```agda
module _
  {l : Level} (R : Semiring l)
  where

  unit-convolution-sequence-Semiring : type-sequence-Semiring R
  unit-convolution-sequence-Semiring = dirac-sequence-Semiring R 0
```

## Properties

### Commutativity

If `a` and `b` _totally commute_ (i.e. if `aᵢbⱼ = bⱼaᵢ` for all `i j : ℕ`) then
`a ⋆ b = b ⋆ a`

```agda
module _
  {l : Level} (R : Semiring l) (a b : type-sequence-Semiring R)
  (H : all-commute-sequence-Semiring R a b)
  where abstract

  htpy-commute-mul-convolution-sequence-Semiring :
    mul-convolution-sequence-Semiring R a b ~
    mul-convolution-sequence-Semiring R b a
  htpy-commute-mul-convolution-sequence-Semiring n =
    equational-reasoning
      sum-finite-Semiring
        ( R)
        ( finite-type-binary-sum-decomposition-ℕ n)
        ( λ (i , j , j+i=n) → mul-Semiring R (a i) (b j))
      ＝
        sum-finite-Semiring
          ( R)
          ( finite-type-binary-sum-decomposition-ℕ n)
          ( λ (i , j , j+i=n) → mul-Semiring R (a j) (b i))
        by
          sum-aut-finite-Semiring
            ( R)
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( aut-swap-binary-sum-decomposition-ℕ n)
            ( _)
      ＝
        sum-finite-Semiring
          ( R)
          ( finite-type-binary-sum-decomposition-ℕ n)
          ( λ (i , j , j+i=n) → mul-Semiring R (b i) (a j))
        by
          htpy-sum-finite-Semiring R _
            ( λ (i , j , j+i=n) → H j i)

  commute-mul-convolution-sequence-Semiring :
    mul-convolution-sequence-Semiring R a b ＝
    mul-convolution-sequence-Semiring R b a
  commute-mul-convolution-sequence-Semiring =
    eq-htpy htpy-commute-mul-convolution-sequence-Semiring
```

### Unit laws

```agda
module _
  {l : Level} (R : Semiring l) (a : type-sequence-Semiring R)
  where abstract

  htpy-left-unit-law-convolution-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( unit-convolution-sequence-Semiring R)
      ( a) ~
    a
  htpy-left-unit-law-convolution-sequence-Semiring n =
    equational-reasoning
      sum-finite-Semiring R
        ( finite-type-binary-sum-decomposition-ℕ n)
        ( λ (i , j , j+i=n) →
          mul-Semiring R
            ( unit-convolution-sequence-Semiring R i)
            ( a j))
      ＝
        add-Semiring R
          ( sum-fin-sequence-type-Semiring R
            ( n)
            ( λ k →
              mul-Semiring R (zero-Semiring R) _))
          ( mul-Semiring R (one-Semiring R) (a n))
          by
            eq-sum-finite-sum-count-Semiring R
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( count-reverse-binary-sum-decomposition-ℕ n)
              ( _)
      ＝
        add-Semiring R
          ( sum-fin-sequence-type-Semiring R
            ( n)
            ( λ _ → zero-Semiring R))
          ( a n)
          by
            ap-add-Semiring R
              ( htpy-sum-fin-sequence-type-Semiring R n
                ( λ _ → left-zero-law-mul-Semiring R _))
              ( left-unit-law-mul-Semiring R _)
      ＝
        add-Semiring R
          ( zero-Semiring R)
          ( a n)
          by
            ap-add-Semiring R
              ( sum-zero-fin-sequence-type-Semiring R n)
              ( refl)
      ＝ a n by left-unit-law-add-Semiring R _

  left-unit-law-convolution-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( unit-convolution-sequence-Semiring R)
      ( a) ＝
    a
  left-unit-law-convolution-sequence-Semiring =
    eq-htpy (htpy-left-unit-law-convolution-sequence-Semiring)

  right-unit-law-convolution-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( a)
      ( unit-convolution-sequence-Semiring R) ＝
    a
  right-unit-law-convolution-sequence-Semiring =
    commute-mul-convolution-sequence-Semiring
      ( R)
      ( a)
      ( unit-convolution-sequence-Semiring R)
      ( is-central-dirac-sequence-Semiring R a 0) ∙
    left-unit-law-convolution-sequence-Semiring
```

### Associativity

```agda
module _
  {l : Level} (R : Semiring l) (a b c : type-sequence-Semiring R)
  where abstract

  htpy-associative-mul-convolution-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( mul-convolution-sequence-Semiring R a b)
      ( c) ~
    mul-convolution-sequence-Semiring R
      ( a)
      ( mul-convolution-sequence-Semiring R b c)
  htpy-associative-mul-convolution-sequence-Semiring n =
    let
      _*R_ :
        type-Semiring R → type-Semiring R →
        type-Semiring R
      _*R_ = mul-Semiring R
    in equational-reasoning
      sum-finite-Semiring
        ( R)
        ( finite-type-binary-sum-decomposition-ℕ n)
        ( λ (i , j , _) →
          ( sum-finite-Semiring
            ( R)
            ( finite-type-binary-sum-decomposition-ℕ i)
            ( λ (k , l , _) → a k *R b l)) *R
          c j)
      ＝
        sum-finite-Semiring
          ( R)
          ( finite-type-binary-sum-decomposition-ℕ n)
          ( λ (i , j , _) →
            ( sum-finite-Semiring
              ( R)
              ( finite-type-binary-sum-decomposition-ℕ i)
              ( λ (k , l , _) → (a k *R b l) *R c j)))
        by
          htpy-sum-finite-Semiring R _
            ( λ (i , j , _) →
              right-distributive-mul-sum-finite-Semiring R _ _
                ( c j))
      ＝
        sum-finite-Semiring
          ( R)
          ( Σ-Finite-Type
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ i))
          ( λ ((i , j , _) , k , l , _) → (a k *R b l) *R c j)
        by
          inv
            ( sum-Σ-finite-Semiring
              ( R)
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( λ (i , _ , _) → finite-type-binary-sum-decomposition-ℕ i)
              ( _))
      ＝
        sum-finite-Semiring
            ( R)
            ( Σ-Finite-Type
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ j))
            ( λ ((i , j , _) , k , l , _) → (a k *R b l) *R c i)
        by
          sum-equiv-finite-Semiring R _ _
            ( equiv-binary-sum-decomposition-pr1-pr2 n)
            ( _)
      ＝
        sum-finite-Semiring
          ( R)
          ( Σ-Finite-Type
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ j))
          ( λ ((i , j , _) , k , l , _) → a k *R (b l *R c i))
        by
          htpy-sum-finite-Semiring R _
            ( λ ((i , j , _) , k , l , _) →
              associative-mul-Semiring R _ _ _)
      ＝
        sum-finite-Semiring
          ( R)
          ( Σ-Finite-Type
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ j))
          ( λ ((i , j , _) , k , l , _) → a i *R (b k *R c l))
        by
          sum-aut-finite-Semiring
            ( R)
            ( Σ-Finite-Type
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ j))
            ( equiv-permute-components-triple-with-sum-pr2 n)
            ( _)
      ＝
        sum-finite-Semiring
          ( R)
          ( finite-type-binary-sum-decomposition-ℕ n)
          ( λ (i , j , _) →
            sum-finite-Semiring
              ( R)
              ( finite-type-binary-sum-decomposition-ℕ j)
              ( λ (k , l , _) → a i *R (b k *R c l)))
        by
          sum-Σ-finite-Semiring
            ( R)
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ (i , j , _) → finite-type-binary-sum-decomposition-ℕ j)
            ( _)
      ＝
        sum-finite-Semiring
          ( R)
          ( finite-type-binary-sum-decomposition-ℕ n)
          ( λ (i , j , _) →
            a i *R
            sum-finite-Semiring
              ( R)
              ( finite-type-binary-sum-decomposition-ℕ j)
              ( λ (k , l , _) → b k *R c l))
        by
          htpy-sum-finite-Semiring R _
            ( λ (i , j , _) →
              inv
                ( left-distributive-mul-sum-finite-Semiring
                  ( R)
                  ( _)
                  ( _)
                  ( _)))

  associative-mul-convolution-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( mul-convolution-sequence-Semiring R a b)
      ( c) ＝
    mul-convolution-sequence-Semiring R
      ( a)
      ( mul-convolution-sequence-Semiring R b c)
  associative-mul-convolution-sequence-Semiring =
    eq-htpy htpy-associative-mul-convolution-sequence-Semiring
```

### Zero laws

```agda
module _
  {l : Level} (R : Semiring l) (a : type-sequence-Semiring R)
  where abstract

  htpy-left-zero-law-convolution-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( zero-sequence-Semiring R)
      ( a) ~
    zero-sequence-Semiring R
  htpy-left-zero-law-convolution-sequence-Semiring n =
    htpy-sum-finite-Semiring R _
      ( λ (i , j , _) → left-zero-law-mul-Semiring R _) ∙
    sum-zero-finite-Semiring R _

  left-zero-law-convolution-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( zero-sequence-Semiring R)
      ( a) ＝
    zero-sequence-Semiring R
  left-zero-law-convolution-sequence-Semiring =
    eq-htpy htpy-left-zero-law-convolution-sequence-Semiring

  right-zero-law-convolution-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( a)
      ( zero-sequence-Semiring R) ＝
    zero-sequence-Semiring R
  right-zero-law-convolution-sequence-Semiring =
    commute-mul-convolution-sequence-Semiring
      ( R)
      ( _)
      ( _)
      ( is-central-zero-sequence-Semiring R a) ∙
    left-zero-law-convolution-sequence-Semiring
```

### Distributivity

```agda
module _
  {l : Level} (R : Semiring l) (a b c : type-sequence-Semiring R)
  where abstract

  htpy-left-distributive-convolution-add-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( a)
      ( add-sequence-Semiring R b c) ~
    add-sequence-Semiring R
      ( mul-convolution-sequence-Semiring R a b)
      ( mul-convolution-sequence-Semiring R a c)
  htpy-left-distributive-convolution-add-sequence-Semiring n =
    htpy-sum-finite-Semiring R _
      ( λ _ → left-distributive-mul-add-Semiring R _ _ _) ∙
    interchange-sum-add-finite-Semiring R _ _ _

  left-distributive-convolution-add-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( a)
      ( add-sequence-Semiring R b c) ＝
    add-sequence-Semiring R
      ( mul-convolution-sequence-Semiring R a b)
      ( mul-convolution-sequence-Semiring R a c)
  left-distributive-convolution-add-sequence-Semiring =
    eq-htpy htpy-left-distributive-convolution-add-sequence-Semiring

  htpy-right-distributive-convolution-add-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( add-sequence-Semiring R a b)
      ( c) ~
    add-sequence-Semiring R
      ( mul-convolution-sequence-Semiring R a c)
      ( mul-convolution-sequence-Semiring R b c)
  htpy-right-distributive-convolution-add-sequence-Semiring n =
    htpy-sum-finite-Semiring R _
      ( λ _ → right-distributive-mul-add-Semiring R _ _ _) ∙
    interchange-sum-add-finite-Semiring R _ _ _

  right-distributive-convolution-add-sequence-Semiring :
    mul-convolution-sequence-Semiring R
      ( add-sequence-Semiring R a b)
      ( c) ＝
    add-sequence-Semiring R
      ( mul-convolution-sequence-Semiring R a c)
      ( mul-convolution-sequence-Semiring R b c)
  right-distributive-convolution-add-sequence-Semiring =
    eq-htpy htpy-right-distributive-convolution-add-sequence-Semiring
```

### The semiring of sequences in a semirings under convolution

```agda
module _
  {l : Level} (R : Semiring l)
  where

  has-associative-mul-convolution-sequence-Semiring :
    has-associative-mul (type-sequence-Semiring R)
  has-associative-mul-convolution-sequence-Semiring =
    ( mul-convolution-sequence-Semiring R ,
      associative-mul-convolution-sequence-Semiring R)

  is-unital-mul-convolution-sequence-Semiring :
    is-unital (mul-convolution-sequence-Semiring R)
  is-unital-mul-convolution-sequence-Semiring =
    ( unit-convolution-sequence-Semiring R ,
      left-unit-law-convolution-sequence-Semiring R ,
      right-unit-law-convolution-sequence-Semiring R)

  has-mul-convolution-additive-commutative-monoid-sequence-Semiring :
    has-mul-Commutative-Monoid
      ( additive-commutative-monoid-sequence-Semiring R)
  has-mul-convolution-additive-commutative-monoid-sequence-Semiring =
    ( has-associative-mul-convolution-sequence-Semiring ,
      is-unital-mul-convolution-sequence-Semiring ,
      left-distributive-convolution-add-sequence-Semiring R ,
      right-distributive-convolution-add-sequence-Semiring R)

  zero-laws-convolution-additive-commutative-monoid-sequence-Semiring :
    zero-laws-Commutative-Monoid
      ( additive-commutative-monoid-sequence-Semiring R)
      ( has-mul-convolution-additive-commutative-monoid-sequence-Semiring)
  zero-laws-convolution-additive-commutative-monoid-sequence-Semiring =
    ( left-zero-law-convolution-sequence-Semiring R ,
      right-zero-law-convolution-sequence-Semiring R)

  convolution-sequence-Semiring : Semiring l
  convolution-sequence-Semiring =
    ( additive-commutative-monoid-sequence-Semiring R ,
      has-mul-convolution-additive-commutative-monoid-sequence-Semiring ,
      zero-laws-convolution-additive-commutative-monoid-sequence-Semiring)
```
