# The fundamental theorem of arithmetic

```agda
module elementary-number-theory.fundamental-theorem-of-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-strong-induction-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.total-decidable-poset-natural-numbers

open import foundation.cartesian-product-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels
open import foundation.unit-type

open import lists.functoriality-lists
open import lists.lists
open import lists.predicates-on-lists
open import lists.sorted-lists
```

</details>

## Idea

The **fundamental theorem of arithmetic** asserts that every nonzero natural
number can be written as a product of primes, and this product is unique up to
the order of the factors.

The uniqueness of the prime factorization of a natural number can be expressed
in several ways:

- We can find a unique list of primes `p₁ ≤ p₂ ≤ ⋯ ≤ pᵢ` of which the product is
  equal to `n`
- The type of finite sets `X` equipped with functions `p : X → Σ ℕ is-prime-ℕ`
  and `m : X → positive-ℕ` such that the product of `pₓᵐ⁽ˣ⁾` is equal to `n` is
  contractible.

Note that the univalence axiom is neccessary to prove the second uniqueness
property of prime factorizations.

## Definitions

### Prime decomposition of a natural number with list

```agda
is-prime-list-ℕ :
  list ℕ → UU lzero
is-prime-list-ℕ = for-all-list ℕ is-prime-ℕ-Prop

mul-list-ℕ :
  list ℕ → ℕ
mul-list-ℕ = fold-list 1 mul-ℕ

is-decomposition-list-ℕ :
  ℕ → list ℕ → UU lzero
is-decomposition-list-ℕ x l =
  mul-list-ℕ l ＝ x

is-prime-decomposition-list-ℕ :
  ℕ → list ℕ → UU lzero
is-prime-decomposition-list-ℕ x l =
  is-sorted-list ℕ-total-decidable-Poset l ×
  ( is-prime-list-ℕ l ×
    is-decomposition-list-ℕ x l)
```

### Nontrivial divisors

Nontrivial divisors of a natural number are divisors strictly greater than `1`.

```agda
is-nontrivial-divisor-ℕ : (n x : ℕ) → UU lzero
is-nontrivial-divisor-ℕ n x = (le-ℕ 1 x) × (div-ℕ x n)

is-decidable-is-nontrivial-divisor-ℕ :
  (n x : ℕ) → is-decidable (is-nontrivial-divisor-ℕ n x)
is-decidable-is-nontrivial-divisor-ℕ n x =
  is-decidable-prod (is-decidable-le-ℕ 1 x) (is-decidable-div-ℕ x n)

is-nontrivial-divisor-diagonal-ℕ :
  (n : ℕ) → le-ℕ 1 n → is-nontrivial-divisor-ℕ n n
pr1 (is-nontrivial-divisor-diagonal-ℕ n H) = H
pr2 (is-nontrivial-divisor-diagonal-ℕ n H) = refl-div-ℕ n
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
is-nonzero-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → is-nonzero-ℕ (nat-least-nontrivial-divisor-ℕ n H)
is-nonzero-least-nontrivial-divisor-ℕ n H =
  is-nonzero-div-ℕ
    ( nat-least-nontrivial-divisor-ℕ n H)
    ( n)
    ( div-least-nontrivial-divisor-ℕ n H)
    ( λ { refl → H})
```

### The least nontrivial divisor of a number `> 1` is prime

```agda
is-prime-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → is-prime-ℕ (nat-least-nontrivial-divisor-ℕ n H)
pr1 (is-prime-least-nontrivial-divisor-ℕ n H x) (K , L) =
  map-right-unit-law-coprod-is-empty
    ( is-one-ℕ x)
    ( le-ℕ 1 x)
    ( λ p →
      contradiction-le-ℕ x l
        ( le-div-ℕ x l
          ( is-nonzero-least-nontrivial-divisor-ℕ n H)
          ( L)
          ( K))
        ( is-minimal-least-nontrivial-divisor-ℕ n H x p
          ( transitive-div-ℕ x l n L (div-least-nontrivial-divisor-ℕ n H))))
    ( eq-or-le-leq-ℕ' 1 x
      ( leq-one-div-ℕ x n
        ( transitive-div-ℕ x l n L
          ( div-least-nontrivial-divisor-ℕ n H))
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

### The fundamental theorem of arithmetic

```agda
is-prime-list-primes-ℕ :
  (l : list Prime-ℕ) → is-prime-list-ℕ (map-list nat-Prime-ℕ l)
is-prime-list-primes-ℕ nil = raise-star
is-prime-list-primes-ℕ (cons x l) =
  (is-prime-Prime-ℕ x) , (is-prime-list-primes-ℕ l)

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

is-prime-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ)
  (p : leq-ℕ 1 x) →
  is-prime-list-ℕ (list-fundamental-theorem-arithmetic-ℕ x p)
is-prime-list-fundamental-theorem-arithmetic-ℕ x p =
  is-prime-list-primes-ℕ (list-primes-fundamental-theorem-arithmetic-ℕ x p)

is-sorted-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → (p : leq-ℕ 1 x) →
  is-sorted-list ℕ-total-decidable-Poset (list-fundamental-theorem-arithmetic-ℕ x p)
is-sorted-list-fundamental-theorem-arithmetic-ℕ =
  {!!}
```
