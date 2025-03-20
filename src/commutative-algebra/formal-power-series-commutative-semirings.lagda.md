# Formal power series on commutative semirings

```agda
module commutative-algebra.formal-power-series-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.sums-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.pairs-with-natural-sums

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.dependent-identifications
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.propositions
open import foundation.cartesian-product-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.involutions
open import foundation.sets
open import foundation.equivalences
open import foundation.unit-type
open import foundation.unital-binary-operations
open import foundation.sections
open import foundation.retractions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.commutative-monoids
open import group-theory.semigroups
open import group-theory.function-commutative-monoids

open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A
{{#concept "formal power series" Agda=formal-power-series-Commutative-Semiring WDID=Q1003025 WD="formal power series"}}
in a [commutative semiring](commutative-algebra.commutative-semirings.md) `R` is a
symbolic infinite sum over all `n : ℕ` of `cₙ xⁿ`, where `cₙ : R`. Convergence
of this sum is not relevant, but with the standard definitions of addition and
multiplication for power series, this forms a new commutative semiring.

## Definition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  opaque
    formal-power-series-Commutative-Semiring : UU l
    formal-power-series-Commutative-Semiring = ℕ → type-Commutative-Semiring R

    formal-power-series-coefficients-Commutative-Semiring :
      (ℕ → type-Commutative-Semiring R) → formal-power-series-Commutative-Semiring
    formal-power-series-coefficients-Commutative-Semiring = id

    coefficient-formal-power-series-Commutative-Semiring :
      formal-power-series-Commutative-Semiring → ℕ → type-Commutative-Semiring R
    coefficient-formal-power-series-Commutative-Semiring = id

    coefficient-formal-power-series-coefficients-Commutative-Semiring :
      (c : ℕ → type-Commutative-Semiring R) →
      coefficient-formal-power-series-Commutative-Semiring
        (formal-power-series-coefficients-Commutative-Semiring c) ~ c
    coefficient-formal-power-series-coefficients-Commutative-Semiring _ _ = refl

    eq-formal-power-series-coefficients-Commutative-Semiring :
      (p : formal-power-series-Commutative-Semiring) →
      p ＝
      formal-power-series-coefficients-Commutative-Semiring
        ( coefficient-formal-power-series-Commutative-Semiring p)
    eq-formal-power-series-coefficients-Commutative-Semiring _ = refl

    eq-htpy-coefficients-formal-power-series-Commutative-Semiring :
      ( p q : formal-power-series-Commutative-Semiring) →
      ( coefficient-formal-power-series-Commutative-Semiring p ~
        coefficient-formal-power-series-Commutative-Semiring q) →
      p ＝ q
    eq-htpy-coefficients-formal-power-series-Commutative-Semiring _ _ = eq-htpy

    is-set-formal-power-series-Commutative-Semiring :
      is-set formal-power-series-Commutative-Semiring
    is-set-formal-power-series-Commutative-Semiring =
      is-set-function-type (is-set-type-Set (set-Commutative-Semiring R))

  set-formal-power-series-Commutative-Semiring : Set l
  set-formal-power-series-Commutative-Semiring =
    formal-power-series-Commutative-Semiring ,
    is-set-formal-power-series-Commutative-Semiring
```

## Operations

### Zero formal power series

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  opaque
    unfolding formal-power-series-Commutative-Semiring

    zero-formal-power-series-Commutative-Semiring :
      formal-power-series-Commutative-Semiring R
    zero-formal-power-series-Commutative-Semiring _ =
      zero-Commutative-Semiring R

    eq-coefficient-zero-formal-power-series-Commutative-Semiring :
      zero-formal-power-series-Commutative-Semiring ＝
      formal-power-series-coefficients-Commutative-Semiring
        ( R)
        ( λ _ → zero-Commutative-Semiring R)
    eq-coefficient-zero-formal-power-series-Commutative-Semiring = refl

    htpy-coefficient-zero-formal-power-series-Commutative-Semiring :
      coefficient-formal-power-series-Commutative-Semiring
        ( R)
        ( zero-formal-power-series-Commutative-Semiring) ~
      (λ _ → zero-Commutative-Semiring R)
    htpy-coefficient-zero-formal-power-series-Commutative-Semiring _ = refl
```

### Constant formal power series

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  coefficient-constant-formal-power-series-Commutative-Semiring :
    type-Commutative-Semiring R → ℕ → type-Commutative-Semiring R
  coefficient-constant-formal-power-series-Commutative-Semiring c zero-ℕ = c
  coefficient-constant-formal-power-series-Commutative-Semiring c (succ-ℕ _) =
    zero-Commutative-Semiring R

  opaque
    unfolding formal-power-series-Commutative-Semiring

    constant-formal-power-series-Commutative-Semiring :
      type-Commutative-Semiring R → formal-power-series-Commutative-Semiring R
    constant-formal-power-series-Commutative-Semiring =
      coefficient-constant-formal-power-series-Commutative-Semiring

    eq-coefficient-constant-formal-power-series-Commutative-Semiring :
      (c : type-Commutative-Semiring R) →
      constant-formal-power-series-Commutative-Semiring c ＝
      formal-power-series-coefficients-Commutative-Semiring
        ( R)
        ( coefficient-constant-formal-power-series-Commutative-Semiring c)
    eq-coefficient-constant-formal-power-series-Commutative-Semiring c = refl

  one-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R
  one-formal-power-series-Commutative-Semiring =
    constant-formal-power-series-Commutative-Semiring
      ( one-Commutative-Semiring R)
```

#### The zero formal power series is the constant formal power series for zero

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  opaque
    unfolding formal-power-series-Commutative-Semiring
    unfolding zero-formal-power-series-Commutative-Semiring
    unfolding constant-formal-power-series-Commutative-Semiring

    eq-zero-constant-formal-power-series-Commutative-Semiring :
      constant-formal-power-series-Commutative-Semiring
        R (zero-Commutative-Semiring R) ＝
      zero-formal-power-series-Commutative-Semiring R
    eq-zero-constant-formal-power-series-Commutative-Semiring =
      eq-htpy (λ { zero-ℕ → refl ; (succ-ℕ _) → refl})
```

### Addition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  coefficient-add-formal-power-series-Commutative-Semiring :
    (p q : formal-power-series-Commutative-Semiring R) (n : ℕ) →
    type-Commutative-Semiring R
  coefficient-add-formal-power-series-Commutative-Semiring p q =
    mul-function-Commutative-Monoid
      ( additive-commutative-monoid-Commutative-Semiring R)
      ( ℕ)
      ( coefficient-formal-power-series-Commutative-Semiring R p)
      ( coefficient-formal-power-series-Commutative-Semiring R q)

  opaque
    unfolding formal-power-series-Commutative-Semiring

    add-formal-power-series-Commutative-Semiring :
      formal-power-series-Commutative-Semiring R →
      formal-power-series-Commutative-Semiring R →
      formal-power-series-Commutative-Semiring R
    add-formal-power-series-Commutative-Semiring =
      coefficient-add-formal-power-series-Commutative-Semiring

    eq-coefficient-add-formal-power-series-Commutative-Semiring :
      (p q : formal-power-series-Commutative-Semiring R) →
      add-formal-power-series-Commutative-Semiring p q ＝
      formal-power-series-coefficients-Commutative-Semiring
        ( R)
        ( coefficient-add-formal-power-series-Commutative-Semiring p q)
    eq-coefficient-add-formal-power-series-Commutative-Semiring p q = refl

    htpy-coefficient-add-formal-power-series-Commutative-Semiring :
      (p q : formal-power-series-Commutative-Semiring R) →
      coefficient-formal-power-series-Commutative-Semiring
        ( R)
        ( add-formal-power-series-Commutative-Semiring p q) ~
      coefficient-add-formal-power-series-Commutative-Semiring p q
    htpy-coefficient-add-formal-power-series-Commutative-Semiring p q n = refl
```

#### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  opaque
    unfolding add-formal-power-series-Commutative-Semiring

    commutative-add-formal-power-series-Commutative-Semiring :
      (p q : formal-power-series-Commutative-Semiring R) →
      add-formal-power-series-Commutative-Semiring R p q ＝
      add-formal-power-series-Commutative-Semiring R q p
    commutative-add-formal-power-series-Commutative-Semiring p q =
      commutative-mul-function-Commutative-Monoid
        ( additive-commutative-monoid-Commutative-Semiring R) ℕ _ _
```

#### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  opaque
    unfolding add-formal-power-series-Commutative-Semiring
    unfolding zero-formal-power-series-Commutative-Semiring

    left-unit-law-add-formal-power-series-Commutative-Semiring :
      (p : formal-power-series-Commutative-Semiring R) →
      add-formal-power-series-Commutative-Semiring
        ( R)
        ( zero-formal-power-series-Commutative-Semiring R)
        ( p) ＝ p
    left-unit-law-add-formal-power-series-Commutative-Semiring =
      left-unit-law-mul-function-Commutative-Monoid
        ( additive-commutative-monoid-Commutative-Semiring R)
        ( ℕ)

    right-unit-law-add-formal-power-series-Commutative-Semiring :
      (p : formal-power-series-Commutative-Semiring R) →
      add-formal-power-series-Commutative-Semiring
        ( R)
        ( p)
        ( zero-formal-power-series-Commutative-Semiring R) ＝ p
    right-unit-law-add-formal-power-series-Commutative-Semiring =
      right-unit-law-mul-function-Commutative-Monoid
        ( additive-commutative-monoid-Commutative-Semiring R)
        ( ℕ)
```

#### Associativity

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  opaque
    unfolding formal-power-series-Commutative-Semiring
    unfolding add-formal-power-series-Commutative-Semiring

    associative-add-formal-power-series-Commutative-Semiring :
      (p q r : formal-power-series-Commutative-Semiring R) →
      add-formal-power-series-Commutative-Semiring
        ( R)
        ( add-formal-power-series-Commutative-Semiring R p q)
        ( r) ＝
      add-formal-power-series-Commutative-Semiring
        ( R)
        ( p)
        ( add-formal-power-series-Commutative-Semiring R q r)
    associative-add-formal-power-series-Commutative-Semiring =
      associative-mul-function-Commutative-Monoid
        ( additive-commutative-monoid-Commutative-Semiring R)
        ( ℕ)
```

#### The additive commutative monoid of formal power series

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  semigroup-add-formal-power-series-Commutative-Semiring : Semigroup l
  semigroup-add-formal-power-series-Commutative-Semiring =
    set-formal-power-series-Commutative-Semiring R ,
    add-formal-power-series-Commutative-Semiring R ,
    associative-add-formal-power-series-Commutative-Semiring R

  is-unital-add-formal-power-series-Commutative-Semiring :
    is-unital (add-formal-power-series-Commutative-Semiring R)
  is-unital-add-formal-power-series-Commutative-Semiring =
    zero-formal-power-series-Commutative-Semiring R ,
    left-unit-law-add-formal-power-series-Commutative-Semiring R ,
    right-unit-law-add-formal-power-series-Commutative-Semiring R

  monoid-add-formal-power-series-Commutative-Semiring : Monoid l
  monoid-add-formal-power-series-Commutative-Semiring =
    semigroup-add-formal-power-series-Commutative-Semiring ,
    is-unital-add-formal-power-series-Commutative-Semiring

  commutative-monoid-add-formal-power-series-Commutative-Semiring :
    Commutative-Monoid l
  commutative-monoid-add-formal-power-series-Commutative-Semiring =
    monoid-add-formal-power-series-Commutative-Semiring ,
    commutative-add-formal-power-series-Commutative-Semiring R
```

### Multiplication

```agda


module _
  {l : Level} (R : Commutative-Semiring l)
  (p q : formal-power-series-Commutative-Semiring R)
  where

  coefficient-mul-formal-power-series-Commutative-Semiring :
    ℕ → type-Commutative-Semiring R
  coefficient-mul-formal-power-series-Commutative-Semiring n =
    sum-finite-Commutative-Semiring
      ( R)
      ( finite-type-pair-with-sum-ℕ n)
      ( λ (a , b , _) →
        mul-Commutative-Semiring
          ( R)
          ( coefficient-formal-power-series-Commutative-Semiring R p a)
          ( coefficient-formal-power-series-Commutative-Semiring R q b))

  abstract
    mul-formal-power-series-Commutative-Semiring :
      formal-power-series-Commutative-Semiring R
    mul-formal-power-series-Commutative-Semiring =
      formal-power-series-coefficients-Commutative-Semiring
        ( R)
        ( coefficient-mul-formal-power-series-Commutative-Semiring)

    eq-coefficient-mul-formal-power-series-Commutative-Semiring :
      coefficient-formal-power-series-Commutative-Semiring
        ( R)
        ( mul-formal-power-series-Commutative-Semiring) ~
      coefficient-mul-formal-power-series-Commutative-Semiring
    eq-coefficient-mul-formal-power-series-Commutative-Semiring =
      coefficient-formal-power-series-coefficients-Commutative-Semiring R _
```

#### Associativity

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  (p q r : formal-power-series-Commutative-Semiring R)
  where

  abstract
    associative-mul-formal-power-series-Commutative-Semiring :
      mul-formal-power-series-Commutative-Semiring
        ( R)
        ( mul-formal-power-series-Commutative-Semiring R p q)
        ( r) ＝
      mul-formal-power-series-Commutative-Semiring
        ( R)
        ( p)
        ( mul-formal-power-series-Commutative-Semiring R q r)
    associative-mul-formal-power-series-Commutative-Semiring =
      eq-htpy-coefficients-formal-power-series-Commutative-Semiring
        ( R)
        ( _)
        ( _)
        ( λ n → equational-reasoning
          coeff ((p *fps q) *fps r) n
          ＝
            sum-finite-Commutative-Semiring
              ( R)
              ( finite-type-pair-with-sum-ℕ n)
              ( λ (a , b , _) → coeff (p *fps q) a *R coeff r b)
            by
              eq-coefficient-mul-formal-power-series-Commutative-Semiring
                ( R)
                ( p *fps q)
                ( r)
                ( n)
          ＝
            sum-finite-Commutative-Semiring
              ( R)
              ( finite-type-pair-with-sum-ℕ n)
              ( λ (a , b , _) →
                sum-finite-Commutative-Semiring
                  ( R)
                  ( finite-type-pair-with-sum-ℕ a)
                  ( λ (c , d , _) → (coeff p c *R coeff q d) *R coeff r b))
            by
              ap
                ( sum-finite-Commutative-Semiring R (finite-type-pair-with-sum-ℕ n))
                ( eq-htpy
                  ( λ (a , b , _) →
                    ap-mul-Commutative-Semiring
                      ( R)
                      ( eq-coefficient-mul-formal-power-series-Commutative-Semiring
                        ( R)
                        ( p)
                        ( q)
                        ( a))
                      ( refl) ∙
                    right-distributive-mul-sum-finite-Commutative-Semiring
                      ( R)
                      ( _)
                      ( _)
                      ( coeff r b)))
          ＝
            sum-finite-Commutative-Semiring
              ( R)
              ( Σ-Finite-Type
                ( finite-type-pair-with-sum-ℕ n)
                ( finite-type-pair-with-sum-ℕ ∘ pr1))
              ( λ ((a , b , _) , c , d , _) →
                (coeff p c *R coeff q d) *R coeff r b)
            by
              inv
                ( sum-Σ-finite-Commutative-Semiring
                  ( R)
                  ( finite-type-pair-with-sum-ℕ n)
                  ( finite-type-pair-with-sum-ℕ ∘ pr1)
                  ( _))
          ＝
            sum-finite-Commutative-Semiring
              ( R)
              ( Σ-Finite-Type
                ( finite-type-pair-with-sum-ℕ n)
                ( finite-type-pair-with-sum-ℕ ∘ pr1 ∘ pr2))
              ( λ ((a , b , _) , c , d , _) →
                (coeff p c *R coeff q d) *R coeff r a)
            by
              sum-equiv-finite-Commutative-Semiring R _ _
                ( inv-equiv (equiv-pair-with-sum-pr1-pr2 n))
                ( _)
          ＝
            sum-finite-Commutative-Semiring
              ( R)
              ( Σ-Finite-Type
                ( finite-type-pair-with-sum-ℕ n)
                ( finite-type-pair-with-sum-ℕ ∘ pr1 ∘ pr2))
              ( λ ((a , b , _) , c , d , _) →
                coeff p c *R (coeff q d *R coeff r a))
            by
              ap
                ( sum-finite-Commutative-Semiring R _)
                ( eq-htpy (λ _ → associative-mul-Commutative-Semiring R _ _ _))
          ＝
            sum-finite-Commutative-Semiring
              ( R)
              ( Σ-Finite-Type
                ( finite-type-pair-with-sum-ℕ n)
                ( finite-type-pair-with-sum-ℕ ∘ pr1 ∘ pr2))
              ( λ ((a , b , _) , c , d , _) →
                coeff p a *R (coeff q c *R coeff r d))
            by
              sum-aut-finite-Commutative-Semiring
                ( R)
                ( Σ-Finite-Type
                  ( finite-type-pair-with-sum-ℕ n)
                  ( finite-type-pair-with-sum-ℕ ∘ pr1 ∘ pr2))
                ( equiv-permute-components-triple-with-sum-pr2 n)
                ( _)
          ＝
            sum-finite-Commutative-Semiring
              ( R)
              ( finite-type-pair-with-sum-ℕ n)
              ( λ (a , b , _) →
                sum-finite-Commutative-Semiring
                ( R)
                ( finite-type-pair-with-sum-ℕ b)
                ( λ (c , d , _) → coeff p a *R (coeff q c *R coeff r d)))
            by
              sum-Σ-finite-Commutative-Semiring
                ( R)
                ( finite-type-pair-with-sum-ℕ n)
                ( finite-type-pair-with-sum-ℕ ∘ pr1 ∘ pr2)
                ( λ (a , b , _) (c , d , _) →
                  coeff p a *R (coeff q c *R coeff r d))
          ＝
            sum-finite-Commutative-Semiring
              ( R)
              ( finite-type-pair-with-sum-ℕ n)
              ( λ (a , b , _) →
                coeff p a *R coeff (q *fps r) b)
            by
              ap
                ( sum-finite-Commutative-Semiring
                  ( R)
                  ( finite-type-pair-with-sum-ℕ n))
              ( eq-htpy
                ( λ (a , b , _) →
                  inv
                    ( left-distributive-mul-sum-finite-Commutative-Semiring
                      ( R)
                      ( finite-type-pair-with-sum-ℕ b)
                      ( coeff p a)
                      ( _)) ∙
                  ap
                    ( coeff p a *R_)
                    ( inv
                      ( eq-coefficient-mul-formal-power-series-Commutative-Semiring
                        ( R)
                        ( q)
                        ( r)
                        ( b)))))
          ＝ coeff (p *fps (q *fps r)) n
            by
              inv
                ( eq-coefficient-mul-formal-power-series-Commutative-Semiring
                  ( R)
                  ( p)
                  ( q *fps r)
                  ( n)))
      where
        _*R_ :
          type-Commutative-Semiring R → type-Commutative-Semiring R →
          type-Commutative-Semiring R
        _*R_ = mul-Commutative-Semiring R
        _*fps_ :
          formal-power-series-Commutative-Semiring R →
          formal-power-series-Commutative-Semiring R →
          formal-power-series-Commutative-Semiring R
        _*fps_ = mul-formal-power-series-Commutative-Semiring R
        coeff :
          formal-power-series-Commutative-Semiring R → ℕ → type-Commutative-Semiring R
        coeff = coefficient-formal-power-series-Commutative-Semiring R
```
