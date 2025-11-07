# Geometric sequences in commutative semirings

```agda
module commutative-algebra.geometric-sequences-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.powers-of-elements-commutative-semirings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-semirings

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.arithmetic-sequences-semigroups

open import lists.finite-sequences
open import lists.sequences

open import ring-theory.geometric-sequences-semirings
open import ring-theory.powers-of-elements-semirings
open import ring-theory.semirings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Ideas

A
{{#concept "geometric sequence" Disambiguation="in a commutative semiring" Agda=geometric-sequence-Commutative-Semiring}}
in a [commutative semiring](ring-theory.commutative-semirings.md) is an
[geometric sequence](ring-theory.geometric-sequences-semirings.md) in the
semiring's multiplicative [semigroup](group-theory.semigroups.md).

These are sequences of the form `n ↦ a * rⁿ`, for elements `a`, `r` in the
semiring.

## Definitions

### Geometric sequences in commutative semirings

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  geometric-sequence-Commutative-Semiring : UU l
  geometric-sequence-Commutative-Semiring =
    geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)

  is-geometric-sequence-Commutative-Semiring :
    sequence (type-Commutative-Semiring R) → UU l
  is-geometric-sequence-Commutative-Semiring =
    is-geometric-sequence-Semiring (semiring-Commutative-Semiring R)

module _
  {l : Level} (R : Commutative-Semiring l)
  (u : geometric-sequence-Commutative-Semiring R)
  where

  seq-geometric-sequence-Commutative-Semiring : ℕ → type-Commutative-Semiring R
  seq-geometric-sequence-Commutative-Semiring =
    seq-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( u)

  is-geometric-seq-geometric-sequence-Commutative-Semiring :
    is-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( seq-geometric-sequence-Commutative-Semiring)
  is-geometric-seq-geometric-sequence-Commutative-Semiring =
    is-geometric-seq-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( u)

  common-ratio-geometric-sequence-Commutative-Semiring :
    type-Commutative-Semiring R
  common-ratio-geometric-sequence-Commutative-Semiring =
    common-ratio-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( u)

  is-common-ratio-geometric-sequence-Commutative-Semiring :
    ( n : ℕ) →
    ( seq-geometric-sequence-Commutative-Semiring (succ-ℕ n)) ＝
    ( mul-Commutative-Semiring
      ( R)
      ( seq-geometric-sequence-Commutative-Semiring n)
      ( common-ratio-geometric-sequence-Commutative-Semiring))
  is-common-ratio-geometric-sequence-Commutative-Semiring =
    is-common-ratio-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( u)

  initial-term-geometric-sequence-Commutative-Semiring :
    type-Commutative-Semiring R
  initial-term-geometric-sequence-Commutative-Semiring =
    initial-term-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( u)
```

### The standard geometric sequences in a commutative semiring

The standard geometric sequence with initial term `a` and common factor `r` is
the sequence `u` defined by:

- `u₀ = a`
- `uₙ₊₁ = uₙ * r`

```agda
module _
  {l : Level} (R : Commutative-Semiring l) (a r : type-Commutative-Semiring R)
  where

  standard-geometric-sequence-Commutative-Semiring :
    geometric-sequence-Commutative-Semiring R
  standard-geometric-sequence-Commutative-Semiring =
    standard-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( a)
      ( r)

  seq-standard-geometric-sequence-Commutative-Semiring :
    ℕ → type-Commutative-Semiring R
  seq-standard-geometric-sequence-Commutative-Semiring =
    seq-geometric-sequence-Commutative-Semiring R
      standard-geometric-sequence-Commutative-Semiring

  is-geometric-standard-geometric-sequence-Commutative-Semiring :
    is-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( seq-standard-geometric-sequence-Commutative-Semiring)
  is-geometric-standard-geometric-sequence-Commutative-Semiring =
    is-geometric-seq-geometric-sequence-Commutative-Semiring R
      standard-geometric-sequence-Commutative-Semiring
```

### The geometric sequences `n ↦ a * rⁿ`

```agda
module _
  {l : Level} (R : Commutative-Semiring l) (a r : type-Commutative-Semiring R)
  where

  mul-pow-nat-Commutative-Semiring : ℕ → type-Commutative-Semiring R
  mul-pow-nat-Commutative-Semiring n =
    mul-Commutative-Semiring R a (power-Commutative-Semiring R n r)

  geometric-mul-pow-nat-Commutative-Semiring :
    geometric-sequence-Commutative-Semiring R
  geometric-mul-pow-nat-Commutative-Semiring =
    geometric-mul-pow-nat-Semiring (semiring-Commutative-Semiring R) a r

  initial-term-mul-pow-nat-Commutative-Semiring : type-Commutative-Semiring R
  initial-term-mul-pow-nat-Commutative-Semiring =
    initial-term-geometric-sequence-Commutative-Semiring
      ( R)
      ( geometric-mul-pow-nat-Commutative-Semiring)

  eq-initial-term-mul-pow-nat-Commutative-Semiring :
    initial-term-mul-pow-nat-Commutative-Semiring ＝ a
  eq-initial-term-mul-pow-nat-Commutative-Semiring =
    right-unit-law-mul-Commutative-Semiring R a
```

## Properties

### Any geometric sequence is homotopic to a standard geometric sequence

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  (u : geometric-sequence-Commutative-Semiring R)
  where

  htpy-seq-standard-geometric-sequence-Commutative-Semiring :
    ( seq-geometric-sequence-Commutative-Semiring R
      ( standard-geometric-sequence-Commutative-Semiring R
        ( initial-term-geometric-sequence-Commutative-Semiring R u)
        ( common-ratio-geometric-sequence-Commutative-Semiring R u))) ~
    ( seq-geometric-sequence-Commutative-Semiring R u)
  htpy-seq-standard-geometric-sequence-Commutative-Semiring =
    htpy-seq-standard-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( u)
```

### The nth term of a geometric sequence with initial term `a` and common ratio `r` is `a * rⁿ`

```agda
module _
  {l : Level} (R : Commutative-Semiring l) (a r : type-Commutative-Semiring R)
  where

  htpy-mul-pow-standard-geometric-sequence-Commutative-Semiring :
    mul-pow-nat-Commutative-Semiring R a r ~
    seq-standard-geometric-sequence-Commutative-Semiring R a r
  htpy-mul-pow-standard-geometric-sequence-Commutative-Semiring =
    htpy-mul-pow-standard-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( a)
      ( r)

  initial-term-standard-geometric-sequence-Commutative-Semiring :
    seq-standard-geometric-sequence-Commutative-Semiring R a r 0 ＝ a
  initial-term-standard-geometric-sequence-Commutative-Semiring =
    ( inv (htpy-mul-pow-standard-geometric-sequence-Commutative-Semiring 0)) ∙
    ( eq-initial-term-mul-pow-nat-Commutative-Semiring R a r)
```

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  (u : geometric-sequence-Commutative-Semiring R)
  where

  htpy-mul-pow-geometric-sequence-Commutative-Semiring :
    mul-pow-nat-Commutative-Semiring
      ( R)
      ( initial-term-geometric-sequence-Commutative-Semiring R u)
      ( common-ratio-geometric-sequence-Commutative-Semiring R u) ~
    seq-geometric-sequence-Commutative-Semiring R u
  htpy-mul-pow-geometric-sequence-Commutative-Semiring n =
    ( htpy-mul-pow-standard-geometric-sequence-Commutative-Semiring
      ( R)
      ( initial-term-geometric-sequence-Commutative-Semiring R u)
      ( common-ratio-geometric-sequence-Commutative-Semiring R u)
      ( n)) ∙
    ( htpy-seq-standard-geometric-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( u)
      ( n))
```

### Constant sequences are geometric with common ratio one

```agda
module _
  {l : Level} (R : Commutative-Semiring l) (a : type-Commutative-Semiring R)
  where

  geometric-const-sequence-Commutative-Semiring :
    geometric-sequence-Commutative-Semiring R
  geometric-const-sequence-Commutative-Semiring =
    geometric-const-sequence-Semiring (semiring-Commutative-Semiring R) a
```

### Finite geometric sequences

```agda
module _
  {l : Level} (R : Commutative-Semiring l) (a r : type-Commutative-Semiring R)
  where

  standard-geometric-fin-sequence-Commutative-Semiring :
    (n : ℕ) → fin-sequence (type-Commutative-Semiring R) n
  standard-geometric-fin-sequence-Commutative-Semiring =
    fin-sequence-sequence
      ( seq-standard-geometric-sequence-Commutative-Semiring R a r)

  sum-standard-geometric-fin-sequence-Commutative-Semiring :
    (n : ℕ) → type-Commutative-Semiring R
  sum-standard-geometric-fin-sequence-Commutative-Semiring n =
    sum-fin-sequence-type-Commutative-Semiring R n
      ( standard-geometric-fin-sequence-Commutative-Semiring n)
```

### The sum of a finite geometric sequence

```agda
module _
  {l : Level} (R : Commutative-Semiring l) (a r : type-Commutative-Semiring R)
  where

  abstract
    compute-sum-standard-geometric-fin-sequence-succ-Commutative-Semiring :
      (n : ℕ) →
      sum-standard-geometric-fin-sequence-Commutative-Semiring R
        ( a)
        ( r)
        ( succ-ℕ n) ＝
      add-Commutative-Semiring R
        ( a)
        ( mul-Commutative-Semiring R
          ( r)
          ( sum-standard-geometric-fin-sequence-Commutative-Semiring R a r n))
    compute-sum-standard-geometric-fin-sequence-succ-Commutative-Semiring n =
      equational-reasoning
        sum-standard-geometric-fin-sequence-Commutative-Semiring R
          ( a)
          ( r)
          ( succ-ℕ n)
        ＝
          add-Commutative-Semiring R
            ( term-Fin a r (succ-ℕ n) (zero-Fin n))
            ( sum-fin-sequence-type-Commutative-Semiring R n
              ( λ i → term-Fin a r (succ-ℕ n) (inr-Fin n i)))
          by
            snoc-sum-fin-sequence-type-Commutative-Semiring R n
              ( standard-geometric-fin-sequence-Commutative-Semiring R
                ( a)
                ( r)
                ( succ-ℕ n))
              ( refl)
        ＝
          add-Commutative-Semiring R
            ( term a r 0)
            ( sum-fin-sequence-type-Commutative-Semiring R n
              ( λ i → term a r (succ-ℕ (nat-Fin n i))))
          by
            ap-add-Commutative-Semiring R
              ( ap
                ( seq-standard-geometric-sequence-Commutative-Semiring R a r)
                ( is-zero-nat-zero-Fin {n}))
              ( htpy-sum-fin-sequence-type-Commutative-Semiring R n
                ( λ i → ap (term a r) (nat-inr-Fin n i)))
        ＝
          add-Commutative-Semiring R
            ( a)
            ( sum-fin-sequence-type-Commutative-Semiring R n
              ( λ i →
                mul-Commutative-Semiring R
                  ( a)
                  ( power-Commutative-Semiring R (succ-ℕ (nat-Fin n i)) r)))
            by
              ap-add-Commutative-Semiring R
                ( initial-term-standard-geometric-sequence-Commutative-Semiring
                  ( R)
                  ( a)
                  ( r))
                ( htpy-sum-fin-sequence-type-Commutative-Semiring R n
                  ( λ i →
                    inv
                      ( htpy-mul-pow-standard-geometric-sequence-Commutative-Semiring
                        ( R)
                        ( a)
                        ( r)
                        ( succ-ℕ (nat-Fin n i)))))
        ＝
          add-Commutative-Semiring R
            ( a)
            ( sum-fin-sequence-type-Commutative-Semiring R n
              ( λ i →
                mul-Commutative-Semiring R
                  ( a)
                  ( mul-Commutative-Semiring R
                    ( r)
                    ( power-Commutative-Semiring R (nat-Fin n i) r))))
            by
              ap-add-Commutative-Semiring R
                ( refl)
                ( htpy-sum-fin-sequence-type-Commutative-Semiring R n
                  ( λ i →
                    ap-mul-Commutative-Semiring R
                      ( refl)
                      ( power-succ-Commutative-Semiring' R (nat-Fin n i) r)))
        ＝
          add-Commutative-Semiring R
            ( a)
            ( sum-fin-sequence-type-Commutative-Semiring R n
              ( λ i →
                mul-Commutative-Semiring R
                  ( r)
                  ( mul-Commutative-Semiring R
                    ( a)
                    ( power-Commutative-Semiring R (nat-Fin n i) r))))
            by
              ap-add-Commutative-Semiring R
                ( refl)
                ( htpy-sum-fin-sequence-type-Commutative-Semiring R n
                  ( λ i → left-swap-mul-Commutative-Semiring R _ _ _))
        ＝
          add-Commutative-Semiring R
            ( a)
            ( mul-Commutative-Semiring R
              ( r)
              ( sum-fin-sequence-type-Commutative-Semiring R n
                ( λ i →
                  mul-Commutative-Semiring R
                    ( a)
                    ( power-Commutative-Semiring R (nat-Fin n i) r))))
          by
            ap-add-Commutative-Semiring R
              ( refl)
              ( inv
                ( left-distributive-mul-sum-fin-sequence-type-Commutative-Semiring
                  ( R)
                  ( n)
                  ( r)
                  ( _)))
        ＝
          add-Commutative-Semiring R
            ( a)
            ( mul-Commutative-Semiring R
              ( r)
              ( sum-standard-geometric-fin-sequence-Commutative-Semiring R
                ( a)
                ( r)
                ( n)))
          by
            ap-add-Commutative-Semiring R
              ( refl)
              ( ap-mul-Commutative-Semiring R
                ( refl)
                ( htpy-sum-fin-sequence-type-Commutative-Semiring R n
                  ( htpy-mul-pow-standard-geometric-sequence-Commutative-Semiring
                      ( R)
                      ( a)
                      ( r) ∘
                    nat-Fin n)))
      where
        term :
          type-Commutative-Semiring R → type-Commutative-Semiring R →
          sequence (type-Commutative-Semiring R)
        term a' r' =
          seq-standard-geometric-sequence-Commutative-Semiring R a' r'
        term-Fin :
          type-Commutative-Semiring R → type-Commutative-Semiring R →
          (n : ℕ) → fin-sequence (type-Commutative-Semiring R) n
        term-Fin a' r' =
          standard-geometric-fin-sequence-Commutative-Semiring R a' r'
```
