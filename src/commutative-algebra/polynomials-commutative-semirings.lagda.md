# Polynomials in commutative semirings

```agda
module commutative-algebra.polynomials-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.formal-power-series-commutative-semirings
open import commutative-algebra.powers-of-elements-commutative-semirings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.empty-types
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.propositional-truncations
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import elementary-number-theory.maximum-natural-numbers
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
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
  {l : Level} (R : Commutative-Semiring l)
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

  polynomial-Commutative-Semiring : UU l
  polynomial-Commutative-Semiring =
    type-subtype is-polynomial-prop-formal-power-series-Commutative-Semiring

  polynomial-add-degree-formal-power-series-Commutative-Semiring :
    (p : formal-power-series-Commutative-Semiring R) →
    (N : ℕ) →
    ( (n : ℕ) →
      is-zero-Commutative-Semiring R
        ( coefficient-formal-power-series-Commutative-Semiring p (n +ℕ N))) →
    polynomial-Commutative-Semiring
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

  is-polynomial-formal-power-series-polynomial-Commutative-Semiring :
    is-polynomial-formal-power-series-Commutative-Semiring
      ( R)
      ( formal-power-series-polynomial-Commutative-Semiring)
  is-polynomial-formal-power-series-polynomial-Commutative-Semiring = pr2 p
```

## Properties

### The zero polynomial

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-polynomial-Commutative-Semiring : polynomial-Commutative-Semiring R
  zero-polynomial-Commutative-Semiring =
    polynomial-add-degree-formal-power-series-Commutative-Semiring R
      ( zero-formal-power-series-Commutative-Semiring R)
      ( zero-ℕ)
      ( λ _ → refl)
```

### The one polynomial

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  one-polynomial-Commutative-Semiring : polynomial-Commutative-Semiring R
  one-polynomial-Commutative-Semiring =
    polynomial-add-degree-formal-power-series-Commutative-Semiring R
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
    polynomial-add-degree-formal-power-series-Commutative-Semiring R
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
      ( is-polynomial-prop-formal-power-series-Commutative-Semiring R)
```

### Evaluation of polynomials

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  ev-degree-bound-formal-power-series-Commutative-Semiring :
    (p : formal-power-series-Commutative-Semiring R) →
    type-Commutative-Semiring R →
    Σ ℕ (is-degree-bound-formal-power-series-Commutative-Semiring R p) →
    type-Commutative-Semiring R
  ev-degree-bound-formal-power-series-Commutative-Semiring p x (N , N≤n→pn=0) =
    sum-fin-sequence-type-Commutative-Semiring R N
      ( term-ev-formal-power-series-Commutative-Semiring R p x ∘ nat-Fin N)

  abstract
    eq-ev-degree-bound-formal-power-series-Commutative-Semiring :
      (p : formal-power-series-Commutative-Semiring R) →
      (x : type-Commutative-Semiring R) →
      (b1 b2 :
        Σ ℕ (is-degree-bound-formal-power-series-Commutative-Semiring R p)) →
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
                ( term-ev-formal-power-series-Commutative-Semiring R p x ∘
                  nat-Fin Nb)
              ＝
                sum-fin-sequence-type-Commutative-Semiring R (Na +ℕ Δ)
                  ( term-ev-formal-power-series-Commutative-Semiring R p x ∘
                    nat-Fin (Na +ℕ Δ))
                by
                  ap
                    (λ N →
                      sum-fin-sequence-type-Commutative-Semiring R N
                        ( term-ev-formal-power-series-Commutative-Semiring
                          ( R)
                          ( p)
                          ( x) ∘
                          nat-Fin N))
                    (inv (commutative-add-ℕ Na Δ ∙ Δ+Na=Nb))
              ＝
                add-Commutative-Semiring R
                  ( sum-fin-sequence-type-Commutative-Semiring R Na
                    ( term-ev-formal-power-series-Commutative-Semiring
                      ( R)
                      ( p)
                      ( x) ∘
                      nat-Fin (Na +ℕ Δ) ∘
                      inl-coproduct-Fin Na Δ))
                  ( sum-fin-sequence-type-Commutative-Semiring R Δ
                    ( term-ev-formal-power-series-Commutative-Semiring
                      ( R)
                      ( p)
                      ( x) ∘
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
                            ( R)
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
    ( formal-power-series-coefficients-Commutative-Semiring c)
    =
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
    is-polynomial-add-polynomial-Commutative-Semiring :
      (p q : polynomial-Commutative-Semiring R) →
      is-polynomial-formal-power-series-Commutative-Semiring
        ( R)
        ( add-formal-power-series-Commutative-Semiring R
          ( formal-power-series-polynomial-Commutative-Semiring p)
          ( formal-power-series-polynomial-Commutative-Semiring q))
    is-polynomial-add-polynomial-Commutative-Semiring
      (p , is-poly-p) (q , is-poly-q)
      =
        let
          open
            do-syntax-trunc-Prop
              ( is-polynomial-prop-formal-power-series-Commutative-Semiring R _)
        in do
          (Np , Hp) ← is-poly-p
          (Nq , Hq) ← is-poly-q
          intro-exists
            ( max-ℕ Np Nq)
            ( λ n max≤n →
              ap-add-Commutative-Semiring R
                ( Hp n
                  ( transitive-leq-ℕ
                    ( Np)
                    ( max-ℕ Np Nq)
                    ( n)
                    ( max≤n)
                    ( left-leq-max-ℕ Np Nq)))
                ( Hq n
                  ( transitive-leq-ℕ
                    ( Nq)
                    ( max-ℕ Np Nq)
                    ( n)
                    ( max≤n)
                    ( right-leq-max-ℕ Np Nq))) ∙
              left-unit-law-add-Commutative-Semiring R _)

  add-polynomial-Commutative-Semiring :
    polynomial-Commutative-Semiring R →
    polynomial-Commutative-Semiring R →
    polynomial-Commutative-Semiring R
  add-polynomial-Commutative-Semiring (p , is-poly-p) (q , is-poly-q) =
    ( add-formal-power-series-Commutative-Semiring R p q ,
      is-polynomial-add-polynomial-Commutative-Semiring
        ( p , is-poly-p)
        ( q , is-poly-q))
```
