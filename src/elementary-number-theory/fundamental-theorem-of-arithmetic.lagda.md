# The fundamental theorem of arithmetic

```agda
module elementary-number-theory.fundamental-theorem-of-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-strong-induction-natural-numbers
open import elementary-number-theory.bezouts-lemma-integers
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-lists-of-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.relatively-prime-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists
open import lists.permutation-lists
open import lists.predicates-on-lists
open import lists.sort-by-insertion-lists
open import lists.sorted-lists
```

</details>

## Idea

The
{{#concept "fundamental theorem of arithmetic" WD="fundamental theorem of arithmetic" WDID=Q670235 Agda=fundamental-theorem-arithmetic-list-ℕ}}
asserts that every
[nonzero](elementary-number-theory.nonzero-natural-numbers.md)
[natural number](elementary-number-theory.natural-numbers.md) can be written as
a [product](elementary-number-theory.products-of-natural-numbers.md) of
[primes](elementary-number-theory.prime-numbers.md), and this product is
[unique](foundation-core.contractible-types.md) up to the order of the factors.

The uniqueness of the prime factorization of a natural number can be expressed
in several ways:

- We can find a unique [list](lists.lists.md) of primes `p₁ ≤ p₂ ≤ ⋯ ≤ pᵢ` of
  which the product is equal to `n`
- The type of [finite sets](univalent-combinatorics.finite-types.md) `X`
  [equipped](foundation.structure.md) with functions `p : X → Σ ℕ is-prime-ℕ`
  and `m : X → positive-ℕ` such that the product of `pₓᵐ⁽ˣ⁾` is
  [equal](foundation-core.identity-types.md) to `n` is contractible.

Note that the [univalence axiom](foundation-core.univalence.md) is necessary to
prove the second uniqueness property of prime factorizations.

The fundamental theorem of arithmetic is the
[80th](literature.100-theorems.md#80) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Definitions

### Prime decomposition of a natural number with lists

A list of natural numbers is a prime decomposition of a natural number `n` if:

- The list is sorted.
- Every element of the list is prime.
- The product of the element of the list is equal to `n`.

```agda
is-prime-list-ℕ :
  list ℕ → UU lzero
is-prime-list-ℕ = for-all-list ℕ is-prime-ℕ-Prop

is-prop-is-prime-list-ℕ :
  (l : list ℕ) → is-prop (is-prime-list-ℕ l)
is-prop-is-prime-list-ℕ = is-prop-for-all-list ℕ is-prime-ℕ-Prop

is-prime-list-primes-ℕ :
  (l : list Prime-ℕ) → is-prime-list-ℕ (map-list nat-Prime-ℕ l)
is-prime-list-primes-ℕ nil = raise-star
is-prime-list-primes-ℕ (cons x l) =
  (is-prime-Prime-ℕ x) , (is-prime-list-primes-ℕ l)

module _
  (x : ℕ)
  (l : list ℕ)
  where

  is-decomposition-list-ℕ :
    UU lzero
  is-decomposition-list-ℕ =
    mul-list-ℕ l ＝ x

  is-prop-is-decomposition-list-ℕ :
    is-prop (is-decomposition-list-ℕ)
  is-prop-is-decomposition-list-ℕ = is-set-ℕ (mul-list-ℕ l) x

  is-prime-decomposition-list-ℕ :
    UU lzero
  is-prime-decomposition-list-ℕ =
    is-sorted-list ℕ-Decidable-Total-Order l ×
    ( is-prime-list-ℕ l ×
      is-decomposition-list-ℕ)

  is-sorted-list-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    is-sorted-list ℕ-Decidable-Total-Order l
  is-sorted-list-is-prime-decomposition-list-ℕ D = pr1 D

  is-prime-list-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    is-prime-list-ℕ l
  is-prime-list-is-prime-decomposition-list-ℕ D =
    pr1 (pr2 D)

  is-decomposition-list-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    is-decomposition-list-ℕ
  is-decomposition-list-is-prime-decomposition-list-ℕ D =
    pr2 (pr2 D)

  is-prop-is-prime-decomposition-list-ℕ :
    is-prop (is-prime-decomposition-list-ℕ)
  is-prop-is-prime-decomposition-list-ℕ =
    is-prop-product
      ( is-prop-is-sorted-list ℕ-Decidable-Total-Order l)
      ( is-prop-product
        ( is-prop-is-prime-list-ℕ l)
        ( is-prop-is-decomposition-list-ℕ))

  is-prime-decomposition-list-ℕ-Prop : Prop lzero
  pr1 is-prime-decomposition-list-ℕ-Prop = is-prime-decomposition-list-ℕ
  pr2 is-prime-decomposition-list-ℕ-Prop = is-prop-is-prime-decomposition-list-ℕ
```

### Nontrivial divisors

Nontrivial divisors of a natural number are divisors strictly greater than `1`.

```agda
is-nontrivial-divisor-ℕ : (n x : ℕ) → UU lzero
is-nontrivial-divisor-ℕ n x = (le-ℕ 1 x) × (div-ℕ x n)

is-prop-is-nontrivial-divisor-ℕ :
  (n x : ℕ) → is-prop (is-nontrivial-divisor-ℕ n x)
is-prop-is-nontrivial-divisor-ℕ n x =
  is-prop-Σ
    ( is-prop-le-ℕ 1 x)
    ( λ p → is-prop-div-ℕ x n (is-nonzero-le-ℕ 1 x p))

is-nontrivial-divisor-ℕ-Prop : (n x : ℕ) → Prop lzero
pr1 (is-nontrivial-divisor-ℕ-Prop n x) = is-nontrivial-divisor-ℕ n x
pr2 (is-nontrivial-divisor-ℕ-Prop n x) = is-prop-is-nontrivial-divisor-ℕ n x

is-decidable-is-nontrivial-divisor-ℕ :
  (n x : ℕ) → is-decidable (is-nontrivial-divisor-ℕ n x)
is-decidable-is-nontrivial-divisor-ℕ n x =
  is-decidable-product (is-decidable-le-ℕ 1 x) (is-decidable-div-ℕ x n)

is-nontrivial-divisor-diagonal-ℕ :
  (n : ℕ) → le-ℕ 1 n → is-nontrivial-divisor-ℕ n n
pr1 (is-nontrivial-divisor-diagonal-ℕ n H) = H
pr2 (is-nontrivial-divisor-diagonal-ℕ n H) = refl-div-ℕ n
```

If `l` is a prime decomposition of `n`, then `l` is a list of nontrivial
divisors of `n`.

```agda
is-list-of-nontrivial-divisors-ℕ :
  ℕ → list ℕ → UU lzero
is-list-of-nontrivial-divisors-ℕ x nil = unit
is-list-of-nontrivial-divisors-ℕ x (cons y l) =
  (is-nontrivial-divisor-ℕ x y) × (is-list-of-nontrivial-divisors-ℕ x l)

is-nontrivial-divisors-div-list-ℕ :
  (x y : ℕ) → div-ℕ x y → (l : list ℕ) →
  is-list-of-nontrivial-divisors-ℕ x l → is-list-of-nontrivial-divisors-ℕ y l
is-nontrivial-divisors-div-list-ℕ x y d nil H = star
is-nontrivial-divisors-div-list-ℕ x y d (cons z l) H =
  ( pr1 (pr1 H) , transitive-div-ℕ z x y d (pr2 (pr1 H))) ,
  is-nontrivial-divisors-div-list-ℕ x y d l (pr2 H)

is-divisor-head-is-decomposition-list-ℕ :
  (x : ℕ) (y : ℕ) (l : list ℕ) →
  is-decomposition-list-ℕ x (cons y l) →
  div-ℕ y x
pr1 (is-divisor-head-is-decomposition-list-ℕ x y l D) =
  mul-list-ℕ l
pr2 (is-divisor-head-is-decomposition-list-ℕ x y l D) =
  commutative-mul-ℕ (mul-list-ℕ l) y ∙ D

is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕ :
  (x : ℕ) (y : ℕ) (l : list ℕ) →
  is-decomposition-list-ℕ x (cons y l) →
  is-prime-list-ℕ (cons y l) →
  is-nontrivial-divisor-ℕ x y
pr1 (is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕ x y l D P) =
  le-one-is-prime-ℕ y (pr1 P)
pr2 (is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕ x y l D P) =
  is-divisor-head-is-decomposition-list-ℕ x y l D

is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕ :
  (x : ℕ) → (l : list ℕ) →
  is-decomposition-list-ℕ x l →
  is-prime-list-ℕ l →
  is-list-of-nontrivial-divisors-ℕ x l
is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕ x nil _ _ = star
is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕ
  ( x)
  ( cons y l)
  ( D)
  ( P) =
  ( is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕ x y l D P ,
    is-nontrivial-divisors-div-list-ℕ
      ( mul-list-ℕ l)
      ( x)
      ( y , D)
      ( l)
      ( is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕ
        ( mul-list-ℕ l)
        ( l)
        ( refl)
        ( pr2 P)))

is-divisor-head-prime-decomposition-list-ℕ :
  (x : ℕ) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  div-ℕ y x
is-divisor-head-prime-decomposition-list-ℕ x y l D =
  is-divisor-head-is-decomposition-list-ℕ
    ( x)
    ( y)
    ( l)
    ( is-decomposition-list-is-prime-decomposition-list-ℕ x (cons y l) D)

is-nontrivial-divisor-head-prime-decomposition-list-ℕ :
  (x : ℕ) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  is-nontrivial-divisor-ℕ x y
is-nontrivial-divisor-head-prime-decomposition-list-ℕ x y l D =
  is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕ
    ( x)
    ( y)
    ( l)
    ( is-decomposition-list-is-prime-decomposition-list-ℕ x (cons y l) D)
    ( is-prime-list-is-prime-decomposition-list-ℕ x (cons y l) D)

is-list-of-nontrivial-divisors-is-prime-decomposition-list-ℕ :
  (x : ℕ) → (l : list ℕ) →
  is-prime-decomposition-list-ℕ x l →
  is-list-of-nontrivial-divisors-ℕ x l
is-list-of-nontrivial-divisors-is-prime-decomposition-list-ℕ x l D =
  is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕ
    ( x)
    ( l)
    ( is-decomposition-list-is-prime-decomposition-list-ℕ x l D)
    ( is-prime-list-is-prime-decomposition-list-ℕ x l D)
```

## Lemmas

### Every natural number strictly greater than `1` has a least nontrivial divisor

```agda
least-nontrivial-divisor-ℕ :
  (n : ℕ) → le-ℕ 1 n → minimal-element-ℕ (is-nontrivial-divisor-ℕ n)
least-nontrivial-divisor-ℕ n H =
  well-ordering-principle-ℕ
    ( is-nontrivial-divisor-ℕ n)
    ( is-decidable-is-nontrivial-divisor-ℕ n)
    ( n , is-nontrivial-divisor-diagonal-ℕ n H)

nat-least-nontrivial-divisor-ℕ : (n : ℕ) → le-ℕ 1 n → ℕ
nat-least-nontrivial-divisor-ℕ n H = pr1 (least-nontrivial-divisor-ℕ n H)

nat-least-nontrivial-divisor-ℕ' : ℕ → ℕ
nat-least-nontrivial-divisor-ℕ' zero-ℕ = 0
nat-least-nontrivial-divisor-ℕ' (succ-ℕ zero-ℕ) = 1
nat-least-nontrivial-divisor-ℕ' (succ-ℕ (succ-ℕ n)) =
  nat-least-nontrivial-divisor-ℕ (succ-ℕ (succ-ℕ n)) star

le-one-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → le-ℕ 1 (nat-least-nontrivial-divisor-ℕ n H)
le-one-least-nontrivial-divisor-ℕ n H =
  pr1 (pr1 (pr2 (least-nontrivial-divisor-ℕ n H)))

div-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → div-ℕ (nat-least-nontrivial-divisor-ℕ n H) n
div-least-nontrivial-divisor-ℕ n H =
  pr2 (pr1 (pr2 (least-nontrivial-divisor-ℕ n H)))

is-minimal-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) (x : ℕ) (K : le-ℕ 1 x) (d : div-ℕ x n) →
  leq-ℕ (nat-least-nontrivial-divisor-ℕ n H) x
is-minimal-least-nontrivial-divisor-ℕ n H x K d =
  pr2 (pr2 (least-nontrivial-divisor-ℕ n H)) x (K , d)
```

### The least nontrivial divisor of a number `> 1` is nonzero

```agda
abstract
  is-nonzero-least-nontrivial-divisor-ℕ :
    (n : ℕ) (H : le-ℕ 1 n) → is-nonzero-ℕ (nat-least-nontrivial-divisor-ℕ n H)
  is-nonzero-least-nontrivial-divisor-ℕ n H =
    is-nonzero-div-ℕ
      ( nat-least-nontrivial-divisor-ℕ n H)
      ( n)
      ( div-least-nontrivial-divisor-ℕ n H)
      ( λ where refl → H)
```

### The least nontrivial divisor of a number `> 1` is prime

```agda
is-prime-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → is-prime-ℕ (nat-least-nontrivial-divisor-ℕ n H)
pr1 (is-prime-least-nontrivial-divisor-ℕ n H x) (K , L) =
  map-right-unit-law-coproduct-is-empty
    ( is-one-ℕ x)
    ( le-ℕ 1 x)
    ( λ p →
      contradiction-le-ℕ x l
        ( le-div-ℕ x l
          ( is-nonzero-least-nontrivial-divisor-ℕ n H)
          ( L)
          ( K))
        ( is-minimal-least-nontrivial-divisor-ℕ n H x p
          ( transitive-div-ℕ x l n (div-least-nontrivial-divisor-ℕ n H) L)))
    ( eq-or-le-leq-ℕ' 1 x
      ( leq-one-div-ℕ x n
        ( transitive-div-ℕ x l n
          ( div-least-nontrivial-divisor-ℕ n H) L)
        ( leq-le-ℕ 1 n H)))
  where
  l = nat-least-nontrivial-divisor-ℕ n H
pr1 (pr2 (is-prime-least-nontrivial-divisor-ℕ n H .1) refl) =
  neq-le-ℕ (le-one-least-nontrivial-divisor-ℕ n H)
pr2 (pr2 (is-prime-least-nontrivial-divisor-ℕ n H .1) refl) =
  div-one-ℕ _
```

### The least prime divisor of a number `1 < n`

```agda
nat-least-prime-divisor-ℕ : (x : ℕ) → le-ℕ 1 x → ℕ
nat-least-prime-divisor-ℕ x H = nat-least-nontrivial-divisor-ℕ x H

is-prime-least-prime-divisor-ℕ :
  (x : ℕ) (H : le-ℕ 1 x) → is-prime-ℕ (nat-least-prime-divisor-ℕ x H)
is-prime-least-prime-divisor-ℕ x H = is-prime-least-nontrivial-divisor-ℕ x H

least-prime-divisor-ℕ : (x : ℕ) → le-ℕ 1 x → Prime-ℕ
pr1 (least-prime-divisor-ℕ x H) = nat-least-prime-divisor-ℕ x H
pr2 (least-prime-divisor-ℕ x H) = is-prime-least-prime-divisor-ℕ x H

div-least-prime-divisor-ℕ :
  (x : ℕ) (H : le-ℕ 1 x) → div-ℕ (nat-least-prime-divisor-ℕ x H) x
div-least-prime-divisor-ℕ x H = div-least-nontrivial-divisor-ℕ x H

quotient-div-least-prime-divisor-ℕ :
  (x : ℕ) (H : le-ℕ 1 x) → ℕ
quotient-div-least-prime-divisor-ℕ x H =
  quotient-div-ℕ
    ( nat-least-prime-divisor-ℕ x H)
    ( x)
    ( div-least-prime-divisor-ℕ x H)

leq-quotient-div-least-prime-divisor-ℕ :
  (x : ℕ) (H : le-ℕ 1 (succ-ℕ x)) →
  leq-ℕ (quotient-div-least-prime-divisor-ℕ (succ-ℕ x) H) x
leq-quotient-div-least-prime-divisor-ℕ x H =
  leq-quotient-div-is-prime-ℕ
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) H)
    ( x)
    ( is-prime-least-prime-divisor-ℕ (succ-ℕ x) H)
    ( div-least-prime-divisor-ℕ (succ-ℕ x) H)
```

## The fundamental theorem of arithmetic (with lists)

### Existence

#### The list given by the fundamental theorem of arithmetic

```agda
list-primes-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → leq-ℕ 1 x → list Prime-ℕ
list-primes-fundamental-theorem-arithmetic-ℕ zero-ℕ ()
list-primes-fundamental-theorem-arithmetic-ℕ (succ-ℕ x) H =
  based-strong-ind-ℕ 1
    ( λ _ → list Prime-ℕ)
    ( nil)
    ( λ n N f →
      cons
        ( least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
        ( f
          ( quotient-div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
          ( leq-one-quotient-div-ℕ
            ( nat-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
            ( succ-ℕ n)
            ( div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
            ( preserves-leq-succ-ℕ 1 n N))
          ( leq-quotient-div-least-prime-divisor-ℕ n (le-succ-leq-ℕ 1 n N))))
    ( succ-ℕ x)
    ( H)

list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → leq-ℕ 1 x → list ℕ
list-fundamental-theorem-arithmetic-ℕ x H =
  map-list nat-Prime-ℕ (list-primes-fundamental-theorem-arithmetic-ℕ x H)
```

#### Computational rules for the list given by the fundamental theorem of arithmetic

```agda
helper-compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  based-strong-ind-ℕ 1
    ( λ _ → list Prime-ℕ)
    ( nil)
    ( λ n N f →
      cons
        ( least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
        ( f
          ( quotient-div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
          ( leq-one-quotient-div-ℕ
            ( nat-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
            ( succ-ℕ n)
            ( div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
            ( preserves-leq-succ-ℕ 1 n N))
          ( leq-quotient-div-least-prime-divisor-ℕ n (le-succ-leq-ℕ 1 n N))))
    ( x)
    ( H) ＝
  list-primes-fundamental-theorem-arithmetic-ℕ x H
helper-compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ (succ-ℕ x) H =
  refl

compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) → (H : 1 ≤-ℕ x) →
  list-primes-fundamental-theorem-arithmetic-ℕ (succ-ℕ x) star ＝
  cons
    ( least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( list-primes-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ
        ( succ-ℕ x)
        ( le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))
compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ x H =
  compute-succ-based-strong-ind-ℕ
    ( 1)
    ( λ _ → list Prime-ℕ)
    ( nil)
    ( λ n N f →
      cons
        ( least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
        ( f
          ( quotient-div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
          ( leq-one-quotient-div-ℕ
            ( nat-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
            ( succ-ℕ n)
            ( div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
            ( preserves-leq-succ-ℕ 1 n N))
          ( leq-quotient-div-least-prime-divisor-ℕ n (le-succ-leq-ℕ 1 n N))))
    ( x)
    ( H)
    ( star) ∙
  ap
    ( cons (least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H)))
    ( helper-compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ
      ( quotient-div-least-prime-divisor-ℕ
        ( succ-ℕ x)
        ( le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))

compute-list-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  list-fundamental-theorem-arithmetic-ℕ (succ-ℕ x) star ＝
  cons
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ
        ( succ-ℕ x)
        ( le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))
compute-list-fundamental-theorem-arithmetic-succ-ℕ x H =
  ap
    ( map-list nat-Prime-ℕ)
    ( compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ x H)
```

#### Proof that the list given by the fundamental theorem of arithmetic is a prime decomposition

```agda
is-prime-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) →
  is-prime-list-ℕ (list-fundamental-theorem-arithmetic-ℕ x H)
is-prime-list-fundamental-theorem-arithmetic-ℕ x H =
  is-prime-list-primes-ℕ (list-primes-fundamental-theorem-arithmetic-ℕ x H)

is-decomposition-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) →
  is-decomposition-list-ℕ x (list-fundamental-theorem-arithmetic-ℕ x H)
is-decomposition-list-fundamental-theorem-arithmetic-ℕ x H =
  based-strong-ind-ℕ' 1
    ( λ n N →
      is-decomposition-list-ℕ n (list-fundamental-theorem-arithmetic-ℕ n N))
    ( refl)
    ( λ n N f →
      tr
        ( λ p → is-decomposition-list-ℕ (succ-ℕ n) p)
        ( inv (compute-list-fundamental-theorem-arithmetic-succ-ℕ n N))
        ( ( ap
            ( ( nat-least-prime-divisor-ℕ
                ( succ-ℕ n)
                ( le-succ-leq-ℕ 1 n N)) *ℕ_)
            ( f
              ( quotient-div-least-prime-divisor-ℕ
                ( succ-ℕ n)
                ( le-succ-leq-ℕ 1 n N))
              ( leq-one-quotient-div-ℕ
                ( nat-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
                ( succ-ℕ n)
                ( div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
                ( preserves-leq-succ-ℕ 1 n N))
              ( leq-quotient-div-least-prime-divisor-ℕ
                ( n)
                ( le-succ-leq-ℕ 1 n N)))) ∙
          eq-quotient-div-ℕ'
            ( nat-least-prime-divisor-ℕ
              ( succ-ℕ n)
              ( le-succ-leq-ℕ 1 n N))
            ( succ-ℕ n)
            ( div-least-prime-divisor-ℕ
              ( succ-ℕ n)
              ( le-succ-leq-ℕ 1 n N))))
    ( x)
    ( H)

is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) →
  is-list-of-nontrivial-divisors-ℕ x (list-fundamental-theorem-arithmetic-ℕ x H)
is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕ x H =
  is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕ
    ( x)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
    ( is-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)
    ( is-prime-list-fundamental-theorem-arithmetic-ℕ x H)

is-least-element-list-least-prime-divisor-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (l : list ℕ) →
  is-list-of-nontrivial-divisors-ℕ
    ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( l) →
  is-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( l)
is-least-element-list-least-prime-divisor-ℕ x H nil D = raise-star
is-least-element-list-least-prime-divisor-ℕ x H (cons y l) D =
  is-minimal-least-nontrivial-divisor-ℕ
    ( succ-ℕ x)
    ( le-succ-leq-ℕ 1 x H)
    ( y)
    ( pr1 (pr1 D))
    ( transitive-div-ℕ
      ( y)
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( succ-ℕ x)
      ( div-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H)))
      ( pr2 (pr1 D))) ,
  is-least-element-list-least-prime-divisor-ℕ x H l (pr2 D)

is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  is-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))
is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕ x H =
  is-least-element-list-least-prime-divisor-ℕ
    ( x)
    ( H)
    ( list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))
    ( is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))

is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  is-sorted-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕ x H =
  based-strong-ind-ℕ' 1
    ( λ x H →
      is-sorted-least-element-list
        ( ℕ-Decidable-Total-Order)
        ( list-fundamental-theorem-arithmetic-ℕ x H))
    ( raise-star)
    ( λ n N f →
      tr
        ( λ l →
          is-sorted-least-element-list
            ( ℕ-Decidable-Total-Order)
            ( l))
        ( inv (compute-list-fundamental-theorem-arithmetic-succ-ℕ n N))
        ( is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕ n N ,
          f
            ( quotient-div-least-prime-divisor-ℕ
              ( succ-ℕ n)
              ( le-succ-leq-ℕ 1 n N))
            ( leq-one-quotient-div-ℕ
              ( nat-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
              ( succ-ℕ n)
              ( div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
              ( preserves-leq-succ-ℕ 1 n N))
            ( leq-quotient-div-least-prime-divisor-ℕ n (le-succ-leq-ℕ 1 n N))))
    ( x)
    ( H)

is-sorted-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  is-sorted-list
    ( ℕ-Decidable-Total-Order)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
is-sorted-list-fundamental-theorem-arithmetic-ℕ x H =
  is-sorted-list-is-sorted-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
    ( is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕ x H)

is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) →
  is-prime-decomposition-list-ℕ x (list-fundamental-theorem-arithmetic-ℕ x H)
pr1 (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H) =
  is-sorted-list-fundamental-theorem-arithmetic-ℕ x H
pr1 (pr2 (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)) =
  is-prime-list-fundamental-theorem-arithmetic-ℕ x H
pr2 (pr2 (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)) =
  is-decomposition-list-fundamental-theorem-arithmetic-ℕ x H
```

### Uniqueness

#### Definition of the type of prime decomposition of an integer

```agda
prime-decomposition-list-ℕ :
  (x : ℕ) → (leq-ℕ 1 x) → UU lzero
prime-decomposition-list-ℕ x _ =
  Σ (list ℕ) (λ l → is-prime-decomposition-list-ℕ x l)
```

#### `prime-decomposition-list-ℕ n` is contractible for every `n`

```agda
prime-decomposition-fundamental-theorem-arithmetic-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) → prime-decomposition-list-ℕ x H
pr1 (prime-decomposition-fundamental-theorem-arithmetic-list-ℕ x H) =
  list-fundamental-theorem-arithmetic-ℕ x H
pr2 (prime-decomposition-fundamental-theorem-arithmetic-list-ℕ x H) =
  is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H

le-one-is-nonempty-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  le-ℕ 1 x
le-one-is-nonempty-prime-decomposition-list-ℕ x H y l D =
  concatenate-le-leq-ℕ
    {x = 1}
    {y = y}
    {z = x}
    ( le-one-is-prime-ℕ
      ( y)
      ( pr1 (is-prime-list-is-prime-decomposition-list-ℕ x (cons y l) D)))
    ( leq-div-ℕ
      ( y)
      ( x)
      ( is-nonzero-leq-one-ℕ x H)
      ( mul-list-ℕ l ,
        ( commutative-mul-ℕ (mul-list-ℕ l) y ∙
          is-decomposition-list-is-prime-decomposition-list-ℕ x (cons y l) D)))

is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x l →
  ( y : ℕ) →
  div-ℕ y x →
  is-prime-ℕ y →
  y ∈-list l
is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕ x H nil D y d p =
  ex-falso
    ( contradiction-le-ℕ
      ( 1)
      ( x)
      ( concatenate-le-leq-ℕ
        {x = 1}
        {y = y}
        {z = x}
        ( le-one-is-prime-ℕ y p)
        ( leq-div-ℕ
          ( y)
          ( x)
          ( is-nonzero-leq-one-ℕ x H)
          ( d)))
        ( leq-eq-ℕ
          ( x)
          ( 1)
          ( inv (is-decomposition-list-is-prime-decomposition-list-ℕ x nil D))))
is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕ x H (cons z l) D y d p =
  rec-coproduct
    ( λ e → tr (λ w → w ∈-list (cons z l)) (inv e) (is-head z l))
    ( λ e →
      is-in-tail
        ( y)
        ( z)
        ( l)
        ( is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕ
          ( quotient-div-ℕ
            ( z)
            ( x)
            ( is-divisor-head-prime-decomposition-list-ℕ x z l D))
          ( leq-one-quotient-div-ℕ
            ( z)
            ( x)
            ( is-divisor-head-prime-decomposition-list-ℕ x z l D)
            ( H))
          ( l)
          ( ( is-sorted-tail-is-sorted-list
              ( ℕ-Decidable-Total-Order)
              ( cons z l)
              ( is-sorted-list-is-prime-decomposition-list-ℕ x (cons z l) D)) ,
            ( pr2
              ( is-prime-list-is-prime-decomposition-list-ℕ x (cons z l) D)) ,
            ( refl))
          ( y)
          ( div-right-factor-coprime-ℕ
            ( y)
            ( z)
            ( mul-list-ℕ l)
            ( tr
              ( λ x → div-ℕ y x)
              ( inv
                ( is-decomposition-list-is-prime-decomposition-list-ℕ
                  ( x)
                  ( cons z l)
                  ( D)))
              ( d))
            ( is-relatively-prime-is-prime-ℕ
              ( y)
              ( z)
              ( p)
              ( pr1
                ( is-prime-list-is-prime-decomposition-list-ℕ x (cons z l) D))
              ( e)))
          ( p)))
    ( has-decidable-equality-ℕ y z)

is-lower-bound-head-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  is-lower-bound-ℕ (is-nontrivial-divisor-ℕ x) y
is-lower-bound-head-prime-decomposition-list-ℕ x H y l D m d =
  transitive-leq-ℕ
    ( y)
    ( nat-least-prime-divisor-ℕ m (pr1 d))
    ( m)
    ( leq-div-ℕ
      ( nat-least-prime-divisor-ℕ m (pr1 d))
      ( m)
      ( is-nonzero-le-ℕ 1 m (pr1 d))
      ( div-least-prime-divisor-ℕ m (pr1 d)))
    ( leq-element-in-list-leq-head-is-sorted-list
      ( ℕ-Decidable-Total-Order)
      ( y)
      ( y)
      ( nat-least-prime-divisor-ℕ m (pr1 d))
      ( l)
      ( is-sorted-list-is-prime-decomposition-list-ℕ x (cons y l) D)
      ( is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕ
        ( x)
        ( H)
        ( cons y l)
        ( D)
        ( nat-least-prime-divisor-ℕ m (pr1 d))
        ( transitive-div-ℕ
          ( nat-least-prime-divisor-ℕ m (pr1 d))
          ( m)
          ( x)
          ( pr2 d)
          ( div-least-nontrivial-divisor-ℕ m (pr1 d)))
        ( is-prime-least-prime-divisor-ℕ m (pr1 d)))
      ( refl-leq-ℕ y))

eq-head-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y z : ℕ) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y p) →
  is-prime-decomposition-list-ℕ x (cons z q) →
  y ＝ z
eq-head-prime-decomposition-list-ℕ x H y z p q I J =
  ap
    ( pr1)
    ( all-elements-equal-minimal-element-ℕ
      ( is-nontrivial-divisor-ℕ-Prop x)
      ( y ,
        is-nontrivial-divisor-head-prime-decomposition-list-ℕ x y p I ,
        is-lower-bound-head-prime-decomposition-list-ℕ x H y p I)
      ( z ,
        is-nontrivial-divisor-head-prime-decomposition-list-ℕ x z q J ,
        is-lower-bound-head-prime-decomposition-list-ℕ x H z q J))

eq-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x p →
  is-prime-decomposition-list-ℕ x q →
  p ＝ q
eq-prime-decomposition-list-ℕ x H nil nil _ _ =
  refl
eq-prime-decomposition-list-ℕ x H (cons y l) nil I J =
  ex-falso
    ( contradiction-le-ℕ
      ( 1)
      ( x)
      ( le-one-is-nonempty-prime-decomposition-list-ℕ x H y l I)
      ( leq-eq-ℕ
        ( x)
        ( 1)
        ( inv ( is-decomposition-list-is-prime-decomposition-list-ℕ x nil J))))
eq-prime-decomposition-list-ℕ x H nil (cons y l) I J =
  ex-falso
    ( contradiction-le-ℕ
      ( 1)
      ( x)
      ( le-one-is-nonempty-prime-decomposition-list-ℕ x H y l J)
      ( leq-eq-ℕ
        ( x)
        ( 1)
        ( inv (is-decomposition-list-is-prime-decomposition-list-ℕ x nil I))))
eq-prime-decomposition-list-ℕ x H (cons y l) (cons z p) I J =
  eq-Eq-list
    ( cons y l)
    ( cons z p)
    ( ( eq-head-prime-decomposition-list-ℕ x H y z l p I J) ,
      ( Eq-eq-list
        ( l)
        ( p)
        ( eq-prime-decomposition-list-ℕ
          ( quotient-div-ℕ
            ( y)
            ( x)
            ( is-divisor-head-prime-decomposition-list-ℕ x y l I))
          ( leq-one-quotient-div-ℕ
            ( y)
            ( x)
            ( is-divisor-head-prime-decomposition-list-ℕ x y l I)
            ( H))
          ( l)
          ( p)
          ( ( is-sorted-tail-is-sorted-list
              ( ℕ-Decidable-Total-Order)
              ( cons y l)
              ( is-sorted-list-is-prime-decomposition-list-ℕ x (cons y l) I)) ,
            pr2 (is-prime-list-is-prime-decomposition-list-ℕ x (cons y l) I) ,
            refl)
          ( ( is-sorted-tail-is-sorted-list
              ( ℕ-Decidable-Total-Order)
              ( cons z p)
              ( is-sorted-list-is-prime-decomposition-list-ℕ x (cons z p) J)) ,
            pr2 (is-prime-list-is-prime-decomposition-list-ℕ x (cons z p) J) ,
            tr
              ( λ y → is-decomposition-list-ℕ y p)
              ( eq-quotient-div-eq-div-ℕ
                ( z)
                ( y)
                ( x)
                ( is-nonzero-is-prime-ℕ
                  ( z)
                  ( pr1
                    ( is-prime-list-is-prime-decomposition-list-ℕ
                      ( x)
                      ( cons z p)
                      ( J))))
                ( inv (eq-head-prime-decomposition-list-ℕ x H y z l p I J))
                ( is-divisor-head-prime-decomposition-list-ℕ x z p J)
                ( is-divisor-head-prime-decomposition-list-ℕ x y l I))
              ( refl)))))

fundamental-theorem-arithmetic-list-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) → is-contr (prime-decomposition-list-ℕ x H)
pr1 (fundamental-theorem-arithmetic-list-ℕ x H) =
  prime-decomposition-fundamental-theorem-arithmetic-list-ℕ x H
pr2 (fundamental-theorem-arithmetic-list-ℕ x H) d =
  eq-type-subtype
    ( is-prime-decomposition-list-ℕ-Prop x)
    ( eq-prime-decomposition-list-ℕ
      ( x)
      ( H)
      ( list-fundamental-theorem-arithmetic-ℕ x H)
      ( pr1 d)
      ( is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)
      ( pr2 d))
```

### The sorted list associated with the concatenation of the prime decomposition of `n` and the prime decomposition of `m` is the prime decomposition of `n *ℕ m`

```agda
is-prime-list-concat-list-ℕ :
  (p q : list ℕ) → is-prime-list-ℕ p → is-prime-list-ℕ q →
  is-prime-list-ℕ (concat-list p q)
is-prime-list-concat-list-ℕ nil q Pp Pq = Pq
is-prime-list-concat-list-ℕ (cons x p) q Pp Pq =
  pr1 Pp , is-prime-list-concat-list-ℕ p q (pr2 Pp) Pq

all-elements-is-prime-list-ℕ :
  (p : list ℕ) → UU lzero
all-elements-is-prime-list-ℕ p = (x : ℕ) → x ∈-list p → is-prime-ℕ x

all-elements-is-prime-list-tail-ℕ :
  (p : list ℕ) (x : ℕ) (P : all-elements-is-prime-list-ℕ (cons x p)) →
  all-elements-is-prime-list-ℕ p
all-elements-is-prime-list-tail-ℕ p x P y I = P y (is-in-tail y x p I)

all-elements-is-prime-list-is-prime-list-ℕ :
  (p : list ℕ) → is-prime-list-ℕ p → all-elements-is-prime-list-ℕ p
all-elements-is-prime-list-is-prime-list-ℕ (cons x p) P .x (is-head .x .p) =
  pr1 P
all-elements-is-prime-list-is-prime-list-ℕ
  ( cons x p)
  ( P)
  ( y)
  ( is-in-tail .y .x .p I) =
  all-elements-is-prime-list-is-prime-list-ℕ p (pr2 P) y I

is-prime-list-all-elements-is-prime-list-ℕ :
  (p : list ℕ) → all-elements-is-prime-list-ℕ p → is-prime-list-ℕ p
is-prime-list-all-elements-is-prime-list-ℕ nil P = raise-star
is-prime-list-all-elements-is-prime-list-ℕ (cons x p) P =
  P x (is-head x p) ,
  is-prime-list-all-elements-is-prime-list-ℕ
    ( p)
    ( all-elements-is-prime-list-tail-ℕ p x P)

is-prime-list-permute-list-ℕ :
  (p : list ℕ) (t : Permutation (length-list p)) → is-prime-list-ℕ p →
  is-prime-list-ℕ (permute-list p t)
is-prime-list-permute-list-ℕ p t P =
  is-prime-list-all-elements-is-prime-list-ℕ
    ( permute-list p t)
    ( λ x I → all-elements-is-prime-list-is-prime-list-ℕ
      ( p)
      ( P)
      ( x)
      ( is-in-list-is-in-permute-list
        ( p)
        ( t)
        ( x)
        ( I)))

is-decomposition-list-concat-list-ℕ :
  (n m : ℕ) (p q : list ℕ) →
  is-decomposition-list-ℕ n p → is-decomposition-list-ℕ m q →
  is-decomposition-list-ℕ (n *ℕ m) (concat-list p q)
is-decomposition-list-concat-list-ℕ n m p q Dp Dq =
  ( eq-mul-list-concat-list-ℕ p q ∙
    ( ap (mul-ℕ (mul-list-ℕ p)) Dq ∙
      ap (λ n → n *ℕ m) Dp))

is-decomposition-list-permute-list-ℕ :
  (n : ℕ) (p : list ℕ) (t : Permutation (length-list p)) →
  is-decomposition-list-ℕ n p →
  is-decomposition-list-ℕ n (permute-list p t)
is-decomposition-list-permute-list-ℕ n p t D =
  inv (invariant-permutation-mul-list-ℕ p t) ∙ D

is-prime-decomposition-list-sort-concatenation-ℕ :
  (x y : ℕ) (H : leq-ℕ 1 x) (I : leq-ℕ 1 y) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x p →
  is-prime-decomposition-list-ℕ y q →
  is-prime-decomposition-list-ℕ
    (x *ℕ y)
    ( insertion-sort-list
      ( ℕ-Decidable-Total-Order)
      ( concat-list p q))
pr1 (is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq) =
  is-sorting-insertion-sort-list ℕ-Decidable-Total-Order (concat-list p q)
pr1
  ( pr2
    ( is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq)) =
  tr
    ( λ p → is-prime-list-ℕ p)
    ( inv
      ( eq-permute-list-permutation-insertion-sort-list
        ( ℕ-Decidable-Total-Order)
        ( concat-list p q)))
    ( is-prime-list-permute-list-ℕ
      ( concat-list p q)
      ( permutation-insertion-sort-list
        ( ℕ-Decidable-Total-Order)
        ( concat-list p q))
      ( is-prime-list-concat-list-ℕ
        ( p)
        ( q)
        ( is-prime-list-is-prime-decomposition-list-ℕ x p Dp)
        ( is-prime-list-is-prime-decomposition-list-ℕ y q Dq)))
pr2
  ( pr2
    ( is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq)) =
  tr
    ( λ p → is-decomposition-list-ℕ (x *ℕ y) p)
    ( inv
      ( eq-permute-list-permutation-insertion-sort-list
        ( ℕ-Decidable-Total-Order)
        ( concat-list p q)))
    ( is-decomposition-list-permute-list-ℕ
      ( x *ℕ y)
      ( concat-list p q)
      ( permutation-insertion-sort-list
        ( ℕ-Decidable-Total-Order)
        ( concat-list p q))
      ( is-decomposition-list-concat-list-ℕ
        ( x)
        ( y)
        ( p)
        ( q)
        ( is-decomposition-list-is-prime-decomposition-list-ℕ x p Dp)
        ( is-decomposition-list-is-prime-decomposition-list-ℕ y q Dq)))

prime-decomposition-list-sort-concatenation-ℕ :
  (x y : ℕ) (H : leq-ℕ 1 x) (I : leq-ℕ 1 y) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x p →
  is-prime-decomposition-list-ℕ y q →
  prime-decomposition-list-ℕ (x *ℕ y) (preserves-leq-mul-ℕ 1 x 1 y H I)
pr1 (prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq) =
  insertion-sort-list ℕ-Decidable-Total-Order (concat-list p q)
pr2 (prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq) =
  is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq
```

## External links

- [Fundamental theorem of arithmetic](https://en.wikipedia.org/wiki/Fundamental_theorem_of_arithmetic)
  at Wikipedia

## References

{{#bibliography}}
