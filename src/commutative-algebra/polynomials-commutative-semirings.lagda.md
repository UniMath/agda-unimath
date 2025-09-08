# Polynomials in commutative semirings

```agda
{-# OPTIONS --lossy-unification #-}

module commutative-algebra.polynomials-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.formal-power-series-commutative-semirings
open import commutative-algebra.powers-of-elements-commutative-semirings
open import commutative-algebra.sums-of-finite-families-of-elements-commutative-semirings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binary-sum-decompositions-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.universe-levels

open import lists.sequences

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "polynomial" WDID=Q43260 WD="polynomial" disambiguation="in a commutative semiring" Agda=polynomial-Commutative-Semiring}}
in a [commutative semiring](commutative-algebra.commutative-semirings.md) is a
[formal power series](commutative-algebra.formal-power-series-commutative-semirings.md)
`Σₙ aₙxⁿ` whose coefficients `aₙ` are zero for sufficiently large `n`.

## Definition

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  is-degree-bound-prop-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R → ℕ → Prop l
  is-degree-bound-prop-formal-power-series-Commutative-Semiring
    ( formal-power-series-coefficients-Commutative-Semiring a)
    ( N) =
    Π-Prop
      ( ℕ)
      ( λ n →
        hom-Prop (leq-ℕ-Prop N n) (is-zero-prop-Commutative-Semiring R (a n)))

  is-degree-bound-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R → ℕ → UU l
  is-degree-bound-formal-power-series-Commutative-Semiring p n =
    type-Prop
      ( is-degree-bound-prop-formal-power-series-Commutative-Semiring p n)

  is-polynomial-prop-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R → Prop l
  is-polynomial-prop-formal-power-series-Commutative-Semiring a =
    ∃ ℕ (is-degree-bound-prop-formal-power-series-Commutative-Semiring a)

  is-polynomial-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R → UU l
  is-polynomial-formal-power-series-Commutative-Semiring a =
    type-Prop (is-polynomial-prop-formal-power-series-Commutative-Semiring a)

polynomial-Commutative-Semiring :
  {l : Level} → (R : Commutative-Semiring l) → UU l
polynomial-Commutative-Semiring R =
  type-subtype
    ( is-polynomial-prop-formal-power-series-Commutative-Semiring {R = R})

module _
  {l : Level} {R : Commutative-Semiring l}
  where

  polynomial-add-degree-formal-power-series-Commutative-Semiring :
    (p : formal-power-series-Commutative-Semiring R) →
    (N : ℕ) →
    ( (n : ℕ) →
      is-zero-Commutative-Semiring R
        ( coefficient-formal-power-series-Commutative-Semiring p (n +ℕ N))) →
    polynomial-Commutative-Semiring R
  polynomial-add-degree-formal-power-series-Commutative-Semiring
    ( formal-power-series-coefficients-Commutative-Semiring p) N H =
    ( formal-power-series-coefficients-Commutative-Semiring p ,
      intro-exists
        ( N)
        ( λ n N≤n →
          let (m , m+N=n) = subtraction-leq-ℕ N n N≤n
          in tr (is-zero-Commutative-Semiring R ∘ p) m+N=n (H m)))

module _
  {l : Level} {R : Commutative-Semiring l}
  (p : polynomial-Commutative-Semiring R)
  where

  formal-power-series-polynomial-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R
  formal-power-series-polynomial-Commutative-Semiring = pr1 p

  coefficient-polynomial-Commutative-Semiring :
    sequence (type-Commutative-Semiring R)
  coefficient-polynomial-Commutative-Semiring =
    coefficient-formal-power-series-Commutative-Semiring
      ( formal-power-series-polynomial-Commutative-Semiring)

  is-polynomial-formal-power-series-polynomial-Commutative-Semiring :
    is-polynomial-formal-power-series-Commutative-Semiring
      ( formal-power-series-polynomial-Commutative-Semiring)
  is-polynomial-formal-power-series-polynomial-Commutative-Semiring = pr2 p
```

## Properties

### The constant zero polynomial

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-polynomial-Commutative-Semiring : polynomial-Commutative-Semiring R
  zero-polynomial-Commutative-Semiring =
    polynomial-add-degree-formal-power-series-Commutative-Semiring
      ( zero-formal-power-series-Commutative-Semiring R)
      ( zero-ℕ)
      ( λ _ → refl)
```

### The constant one polynomial

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  one-polynomial-Commutative-Semiring : polynomial-Commutative-Semiring R
  one-polynomial-Commutative-Semiring =
    polynomial-add-degree-formal-power-series-Commutative-Semiring
      ( one-formal-power-series-Commutative-Semiring R)
      ( 1)
      ( λ _ → refl)
```

### The identity polynomial

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  id-polynomial-Commutative-Semiring : polynomial-Commutative-Semiring R
  id-polynomial-Commutative-Semiring =
    polynomial-add-degree-formal-power-series-Commutative-Semiring
      ( id-formal-power-series-Commutative-Semiring R)
      ( 2)
      ( λ _ → refl)
```

### The set of polynomials

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  set-polynomial-Commutative-Semiring : Set l
  set-polynomial-Commutative-Semiring =
    set-subset
      ( set-formal-power-series-Commutative-Semiring R)
      ( is-polynomial-prop-formal-power-series-Commutative-Semiring)
```

### Evaluation of polynomials

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  ev-degree-bound-formal-power-series-Commutative-Semiring :
    (p : formal-power-series-Commutative-Semiring R) →
    type-Commutative-Semiring R →
    Σ ℕ (is-degree-bound-formal-power-series-Commutative-Semiring p) →
    type-Commutative-Semiring R
  ev-degree-bound-formal-power-series-Commutative-Semiring p x (N , N≤n→pn=0) =
    sum-fin-sequence-type-Commutative-Semiring R N
      ( term-ev-formal-power-series-Commutative-Semiring p x ∘ nat-Fin N)

  abstract
    eq-ev-degree-bound-formal-power-series-Commutative-Semiring :
      (p : formal-power-series-Commutative-Semiring R) →
      (x : type-Commutative-Semiring R) →
      (b1 b2 :
        Σ ℕ (is-degree-bound-formal-power-series-Commutative-Semiring p)) →
      ev-degree-bound-formal-power-series-Commutative-Semiring p x b1 ＝
      ev-degree-bound-formal-power-series-Commutative-Semiring p x b2
    eq-ev-degree-bound-formal-power-series-Commutative-Semiring
      p@(formal-power-series-coefficients-Commutative-Semiring c) x
      (N₁ , N₁≤n→pn=0) (N₂ , N₂≤n→pn=0) =
      rec-coproduct
        ( λ N₁≤N₂ → inv (case N₁ N₁≤n→pn=0 N₂ N₂≤n→pn=0 N₁≤N₂))
        ( λ N₂≤N₁ → case N₂ N₂≤n→pn=0 N₁ N₁≤n→pn=0 N₂≤N₁)
        ( linear-leq-ℕ N₁ N₂)
      where
        case :
          (Na : ℕ)
          (Ha : (n : ℕ) → leq-ℕ Na n → is-zero-Commutative-Semiring R (c n)) →
          (Nb : ℕ) →
          (Hb : (n : ℕ) → leq-ℕ Nb n → is-zero-Commutative-Semiring R (c n)) →
          leq-ℕ Na Nb →
          ev-degree-bound-formal-power-series-Commutative-Semiring
            ( p)
            ( x)
            ( Nb , Hb) ＝
          ev-degree-bound-formal-power-series-Commutative-Semiring
            ( p)
            ( x)
            ( Na , Ha)
        case Na Na≤n→pn=0 Nb Nb≤n→pn=0 Na≤Nb =
          let (Δ , Δ+Na=Nb) = subtraction-leq-ℕ Na Nb Na≤Nb
          in
            equational-reasoning
              sum-fin-sequence-type-Commutative-Semiring R Nb
                ( term-ev-formal-power-series-Commutative-Semiring p x ∘
                  nat-Fin Nb)
              ＝
                sum-fin-sequence-type-Commutative-Semiring R (Na +ℕ Δ)
                  ( term-ev-formal-power-series-Commutative-Semiring p x ∘
                    nat-Fin (Na +ℕ Δ))
                by
                  ap
                    (λ N →
                      sum-fin-sequence-type-Commutative-Semiring R N
                        ( term-ev-formal-power-series-Commutative-Semiring p x ∘
                          nat-Fin N))
                    (inv (commutative-add-ℕ Na Δ ∙ Δ+Na=Nb))
              ＝
                add-Commutative-Semiring R
                  ( sum-fin-sequence-type-Commutative-Semiring R Na
                    ( term-ev-formal-power-series-Commutative-Semiring p x ∘
                      nat-Fin (Na +ℕ Δ) ∘
                      inl-coproduct-Fin Na Δ))
                  ( sum-fin-sequence-type-Commutative-Semiring R Δ
                    ( term-ev-formal-power-series-Commutative-Semiring p x ∘
                      nat-Fin (Na +ℕ Δ) ∘
                      inr-coproduct-Fin Na Δ))
                by
                  split-sum-fin-sequence-type-Commutative-Semiring R Na Δ _
              ＝
                add-Commutative-Semiring R
                  ( ev-degree-bound-formal-power-series-Commutative-Semiring
                    ( p)
                    ( x)
                    ( Na , Na≤n→pn=0))
                  ( sum-fin-sequence-type-Commutative-Semiring R Δ
                    ( λ _ → zero-Commutative-Semiring R))
                by
                  ap-add-Commutative-Semiring R
                    ( htpy-sum-fin-sequence-type-Commutative-Semiring R Na
                      ( λ n →
                        ap
                          ( term-ev-formal-power-series-Commutative-Semiring
                            ( p)
                            ( x))
                          ( nat-inl-coproduct-Fin Na Δ n)))
                    ( htpy-sum-fin-sequence-type-Commutative-Semiring R Δ
                      ( λ n →
                        equational-reasoning
                          mul-Commutative-Semiring R
                            ( c (nat-Fin (Na +ℕ Δ) (inr-coproduct-Fin Na Δ n)))
                            ( power-Commutative-Semiring R
                              ( nat-Fin (Na +ℕ Δ) (inr-coproduct-Fin Na Δ n))
                              ( x))
                          ＝
                            mul-Commutative-Semiring R
                              ( c (Na +ℕ nat-Fin Δ n))
                              ( _)
                            by
                              ap-mul-Commutative-Semiring R
                                ( ap c (nat-inr-coproduct-Fin Na Δ n))
                                ( refl)
                          ＝
                            mul-Commutative-Semiring R
                              ( zero-Commutative-Semiring R)
                              ( _)
                            by
                              ap-mul-Commutative-Semiring R
                                ( Na≤n→pn=0
                                  ( Na +ℕ nat-Fin Δ n)
                                  ( leq-add-ℕ Na _))
                                ( refl)
                          ＝ zero-Commutative-Semiring R
                            by left-zero-law-mul-Commutative-Semiring R _))
              ＝
                add-Commutative-Semiring R
                  ( ev-degree-bound-formal-power-series-Commutative-Semiring
                    ( p)
                    ( x)
                    ( Na , Na≤n→pn=0))
                  ( zero-Commutative-Semiring R)
                by
                  ap-add-Commutative-Semiring R refl
                    ( sum-zero-fin-sequence-type-Commutative-Semiring R Δ)
              ＝
                ev-degree-bound-formal-power-series-Commutative-Semiring
                  ( p)
                  ( x)
                  (Na , Na≤n→pn=0)
                by right-unit-law-add-Commutative-Semiring R _

  ev-polynomial-Commutative-Semiring :
    polynomial-Commutative-Semiring R → type-Commutative-Semiring R →
    type-Commutative-Semiring R
  ev-polynomial-Commutative-Semiring (p , deg-bound-p) x =
    map-universal-property-set-quotient-trunc-Prop
      ( set-Commutative-Semiring R)
      ( ev-degree-bound-formal-power-series-Commutative-Semiring p x)
      ( eq-ev-degree-bound-formal-power-series-Commutative-Semiring p x)
      ( deg-bound-p)

  abstract
    eq-ev-polynomial-degree-bound-Commutative-Semiring :
      (p : polynomial-Commutative-Semiring R) →
      (x : type-Commutative-Semiring R) →
      (N : ℕ) →
      (H : (n : ℕ) → leq-ℕ N n →
        is-zero-Commutative-Semiring R
          ( coefficient-polynomial-Commutative-Semiring p n)) →
      ev-polynomial-Commutative-Semiring p x ＝
      ev-degree-bound-formal-power-series-Commutative-Semiring
        ( formal-power-series-polynomial-Commutative-Semiring p)
        ( x)
        ( N , H)
    eq-ev-polynomial-degree-bound-Commutative-Semiring (p , is-poly-p) x N H =
      ap
        ( λ ipp → ev-polynomial-Commutative-Semiring (p , ipp) x)
        ( all-elements-equal-type-trunc-Prop
          ( is-poly-p)
          ( intro-exists N H)) ∙
      htpy-universal-property-set-quotient-trunc-Prop
        ( set-Commutative-Semiring R)
        ( ev-degree-bound-formal-power-series-Commutative-Semiring p x)
        ( eq-ev-degree-bound-formal-power-series-Commutative-Semiring p x)
        ( N , H)
```

### Truncation of a formal power series into a polynomial

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  truncate-formal-power-series-Commutative-Semiring :
    (n : ℕ) → formal-power-series-Commutative-Semiring R →
    polynomial-Commutative-Semiring R
  truncate-formal-power-series-Commutative-Semiring
    ( n)
    ( formal-power-series-coefficients-Commutative-Semiring c) =
    let
      d : (k : ℕ) → (le-ℕ k n + leq-ℕ n k) → type-Commutative-Semiring R
      d = λ where
        k (inl k<n) → c k
        k (inr n≤k) → zero-Commutative-Semiring R
      deg-bound-d : (k : ℕ) → (H : le-ℕ k n + leq-ℕ n k) → leq-ℕ n k →
        is-zero-Commutative-Semiring R (d k H)
      deg-bound-d = λ where
        k (inl k<n) n≤k → ex-falso (contradiction-le-ℕ k n k<n n≤k)
        k (inr _) _ → refl
    in
      ( formal-power-series-coefficients-Commutative-Semiring
        ( λ k → d k (decide-le-leq-ℕ k n)) ,
        intro-exists n (λ k n≤k → deg-bound-d k (decide-le-leq-ℕ k n) n≤k))
```

### Addition of polynomials

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    degree-bound-add-formal-power-series-Commutative-Semiring :
      (p q : formal-power-series-Commutative-Semiring R) →
      Σ ℕ (is-degree-bound-formal-power-series-Commutative-Semiring p) →
      Σ ℕ (is-degree-bound-formal-power-series-Commutative-Semiring q) →
      Σ ℕ
        ( λ N →
          is-degree-bound-formal-power-series-Commutative-Semiring p N ×
          is-degree-bound-formal-power-series-Commutative-Semiring q N ×
          is-degree-bound-formal-power-series-Commutative-Semiring
            ( add-formal-power-series-Commutative-Semiring p q)
            ( N))
    degree-bound-add-formal-power-series-Commutative-Semiring
      ( formal-power-series-coefficients-Commutative-Semiring p)
      ( formal-power-series-coefficients-Commutative-Semiring q)
      ( Np , Hp)
      ( Nq , Hq) =
      let
        N = max-ℕ Np Nq
        case r Nr Hr Nr≤N n N≤n = Hr n (transitive-leq-ℕ Nr N n N≤n Nr≤N)
      in
        ( N ,
          case p Np Hp (left-leq-max-ℕ Np Nq) ,
          case q Nq Hq (right-leq-max-ℕ Np Nq) ,
          λ n N≤n →
            ap-add-Commutative-Semiring R
              ( case p Np Hp (left-leq-max-ℕ Np Nq) n N≤n)
              ( case q Nq Hq (right-leq-max-ℕ Np Nq) n N≤n) ∙
            left-unit-law-add-Commutative-Semiring R _)

    is-polynomial-add-polynomial-Commutative-Semiring :
      (p q : polynomial-Commutative-Semiring R) →
      is-polynomial-formal-power-series-Commutative-Semiring
        ( add-formal-power-series-Commutative-Semiring
          ( formal-power-series-polynomial-Commutative-Semiring p)
          ( formal-power-series-polynomial-Commutative-Semiring q))
    is-polynomial-add-polynomial-Commutative-Semiring
      (p , is-poly-p) (q , is-poly-q) =
      let
        open
          do-syntax-trunc-Prop
            ( is-polynomial-prop-formal-power-series-Commutative-Semiring _)
      in do
        (Np , Hp) ← is-poly-p
        (Nq , Hq) ← is-poly-q
        let
          (N , _ , _ , H) =
            degree-bound-add-formal-power-series-Commutative-Semiring
              ( p)
              ( q)
              ( Np , Hp)
              ( Nq , Hq)
        intro-exists N H

  add-polynomial-Commutative-Semiring :
    polynomial-Commutative-Semiring R →
    polynomial-Commutative-Semiring R →
    polynomial-Commutative-Semiring R
  add-polynomial-Commutative-Semiring (p , is-poly-p) (q , is-poly-q) =
    ( add-formal-power-series-Commutative-Semiring p q ,
      is-polynomial-add-polynomial-Commutative-Semiring
        ( p , is-poly-p)
        ( q , is-poly-q))
```

#### The sum of two polynomials, evaluated at `x`, is equal to the sum of each polynomial evaluated at `x`

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    interchange-ev-add-polynomial-Commutative-Semiring :
      (p q : polynomial-Commutative-Semiring R) →
      (x : type-Commutative-Semiring R) →
      ev-polynomial-Commutative-Semiring
        ( add-polynomial-Commutative-Semiring p q)
        ( x) ＝
      add-Commutative-Semiring R
        ( ev-polynomial-Commutative-Semiring p x)
        ( ev-polynomial-Commutative-Semiring q x)
    interchange-ev-add-polynomial-Commutative-Semiring
      pp@(p , is-poly-p) qq@(q , is-poly-q) x =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Semiring R)
              ( ev-polynomial-Commutative-Semiring
                ( add-polynomial-Commutative-Semiring pp qq)
                ( x))
              ( add-Commutative-Semiring R
                ( ev-polynomial-Commutative-Semiring pp x)
                ( ev-polynomial-Commutative-Semiring qq x)))
      in do
        (Np , Hp) ← is-poly-p
        (Nq , Hq) ← is-poly-q
        let
          (N , Hp' , Hq' , H) =
            degree-bound-add-formal-power-series-Commutative-Semiring
              ( p)
              ( q)
              ( Np , Hp)
              ( Nq , Hq)
        equational-reasoning
          ev-polynomial-Commutative-Semiring
            ( add-polynomial-Commutative-Semiring pp qq)
            ( x)
          ＝
            ev-degree-bound-formal-power-series-Commutative-Semiring
              ( add-formal-power-series-Commutative-Semiring p q)
              ( x)
              ( N , H)
            by
              eq-ev-polynomial-degree-bound-Commutative-Semiring _ x N H
          ＝
            sum-fin-sequence-type-Commutative-Semiring R N
              ( λ i → add-Commutative-Semiring R _ _)
            by
              htpy-sum-fin-sequence-type-Commutative-Semiring R N
                ( λ i →
                  right-distributive-mul-add-Commutative-Semiring R _ _ _)
          ＝
            add-Commutative-Semiring R
              ( ev-degree-bound-formal-power-series-Commutative-Semiring
                ( p)
                ( x)
                ( N , Hp'))
              ( ev-degree-bound-formal-power-series-Commutative-Semiring
                ( q)
                ( x)
                ( N , Hq'))
            by
              inv
                ( interchange-add-sum-fin-sequence-type-Commutative-Semiring
                  ( R)
                  ( N)
                  ( _)
                  ( _))
          ＝
            add-Commutative-Semiring R
              ( ev-polynomial-Commutative-Semiring pp x)
              ( ev-polynomial-Commutative-Semiring qq x)
            by
              ap-add-Commutative-Semiring R
                ( inv
                  ( eq-ev-polynomial-degree-bound-Commutative-Semiring
                    ( pp)
                    ( x)
                    ( N)
                    ( Hp')))
                ( inv
                  ( eq-ev-polynomial-degree-bound-Commutative-Semiring
                    ( qq)
                    ( x)
                    ( N)
                    ( Hq')))
```

### Multiplication of polynomials

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  degree-bound-mul-formal-power-series-Commutative-Semiring :
    (p q : formal-power-series-Commutative-Semiring R) →
    Σ ℕ (is-degree-bound-formal-power-series-Commutative-Semiring p) →
    Σ ℕ (is-degree-bound-formal-power-series-Commutative-Semiring q) →
    Σ ℕ
      ( is-degree-bound-formal-power-series-Commutative-Semiring
        ( mul-formal-power-series-Commutative-Semiring p q))
  degree-bound-mul-formal-power-series-Commutative-Semiring
    ( formal-power-series-coefficients-Commutative-Semiring p)
    ( formal-power-series-coefficients-Commutative-Semiring q)
    ( Np , Hp)
    ( Nq , Hq) =
    ( Nq +ℕ Np ,
      λ n Nq+Np≤n →
        equational-reasoning
          sum-finite-Commutative-Semiring R
            ( finite-type-binary-sum-decomposition-ℕ n)
            ( λ (i , j , j+i=n) → mul-Commutative-Semiring R (p i) (q j))
          ＝
            sum-finite-Commutative-Semiring R
              ( finite-type-binary-sum-decomposition-ℕ n)
              ( λ _ → zero-Commutative-Semiring R)
            by
              htpy-sum-finite-Commutative-Semiring R _
                ( λ (i , j , j+i=n) →
                  rec-coproduct
                    ( λ i<Np →
                      rec-coproduct
                        ( λ j<Nq →
                          ex-falso
                            ( anti-reflexive-le-ℕ
                              ( n)
                              ( tr
                                ( λ m → le-ℕ m n)
                                ( j+i=n)
                                ( concatenate-le-leq-ℕ
                                  ( preserves-le-add-ℕ j<Nq i<Np)
                                  ( Nq+Np≤n)))))
                        ( λ Nq≤j →
                          ap-mul-Commutative-Semiring R refl (Hq j Nq≤j) ∙
                          right-zero-law-mul-Commutative-Semiring R _)
                        ( decide-le-leq-ℕ j Nq))
                    ( λ Np≤i →
                      ap-mul-Commutative-Semiring R (Hp i Np≤i) refl ∙
                      left-zero-law-mul-Commutative-Semiring R _)
                    ( decide-le-leq-ℕ i Np))
          ＝
            zero-Commutative-Semiring R
            by sum-zero-finite-Commutative-Semiring R _)

  abstract
    is-polynomial-mul-polynomial-Commutative-Semiring :
      (p q : polynomial-Commutative-Semiring R) →
      is-polynomial-formal-power-series-Commutative-Semiring
        ( mul-formal-power-series-Commutative-Semiring
          ( formal-power-series-polynomial-Commutative-Semiring p)
          ( formal-power-series-polynomial-Commutative-Semiring q))
    is-polynomial-mul-polynomial-Commutative-Semiring
      (p , is-poly-p) (q , is-poly-q) =
      let
        open
          do-syntax-trunc-Prop
            ( is-polynomial-prop-formal-power-series-Commutative-Semiring
              ( mul-formal-power-series-Commutative-Semiring p q))
      in do
        (Np , Hp) ← is-poly-p
        (Nq , Hq) ← is-poly-q
        unit-trunc-Prop
          ( degree-bound-mul-formal-power-series-Commutative-Semiring
            ( p)
            ( q)
            ( Np , Hp)
            ( Nq , Hq))

  mul-polynomial-Commutative-Semiring :
    polynomial-Commutative-Semiring R →
    polynomial-Commutative-Semiring R →
    polynomial-Commutative-Semiring R
  mul-polynomial-Commutative-Semiring pp@(p , is-poly-p) qq@(q , is-poly-q) =
    ( mul-formal-power-series-Commutative-Semiring p q ,
      is-polynomial-mul-polynomial-Commutative-Semiring pp qq)
```
