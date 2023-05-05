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
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.bezouts-lemma-natural-numbers

open import foundation.cartesian-product-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels
open import foundation.unit-type
open import foundation.equality-dependent-pair-types
open import foundation.propositions
open import foundation.contractible-types
open import foundation.empty-types
open import foundation.coproduct-types

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

is-prop-is-prime-list-ℕ :
  (l : list ℕ) → is-prop (is-prime-list-ℕ l)
is-prop-is-prime-list-ℕ = is-prop-for-all-list ℕ is-prime-ℕ-Prop

mul-list-ℕ :
  list ℕ → ℕ
mul-list-ℕ = fold-list 1 mul-ℕ

is-decomposition-list-ℕ :
  ℕ → list ℕ → UU lzero
is-decomposition-list-ℕ x l =
  mul-list-ℕ l ＝ x

is-prop-is-decomposition-list-ℕ :
  (x : ℕ) → (l : list ℕ) →
  is-prop (is-decomposition-list-ℕ x l)
is-prop-is-decomposition-list-ℕ x l = is-set-ℕ (mul-list-ℕ l) x

is-prime-decomposition-list-ℕ :
  ℕ → list ℕ → UU lzero
is-prime-decomposition-list-ℕ x l =
  is-sorted-list ℕ-total-decidable-Poset l ×
  ( is-prime-list-ℕ l ×
    is-decomposition-list-ℕ x l)

is-prop-is-prime-decomposition-list-ℕ :
  (x : ℕ) → (l : list ℕ) →
  is-prop (is-prime-decomposition-list-ℕ x l)
is-prop-is-prime-decomposition-list-ℕ x l =
  is-prop-prod
    ( is-prop-is-sorted-list ℕ-total-decidable-Poset l)
    ( is-prop-prod
      ( is-prop-is-prime-list-ℕ l)
      ( is-prop-is-decomposition-list-ℕ x l))
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
  is-decidable-prod (is-decidable-le-ℕ 1 x) (is-decidable-div-ℕ x n)

is-nontrivial-divisor-diagonal-ℕ :
  (n : ℕ) → le-ℕ 1 n → is-nontrivial-divisor-ℕ n n
pr1 (is-nontrivial-divisor-diagonal-ℕ n H) = H
pr2 (is-nontrivial-divisor-diagonal-ℕ n H) = refl-div-ℕ n

is-nontrivial-divisors-list-ℕ :
  ℕ → list ℕ → UU lzero
is-nontrivial-divisors-list-ℕ x nil = unit
is-nontrivial-divisors-list-ℕ x (cons y l) =
  (is-nontrivial-divisor-ℕ x y) × (is-nontrivial-divisors-list-ℕ x l)

transitive-is-nontrivial-divisors-list-ℕ :
  (x y : ℕ) → div-ℕ x y → (l : list ℕ) →
  is-nontrivial-divisors-list-ℕ x l → is-nontrivial-divisors-list-ℕ y l
transitive-is-nontrivial-divisors-list-ℕ x y d nil H = star
transitive-is-nontrivial-divisors-list-ℕ x y d (cons z l) H =
  ( pr1 (pr1 H) , transitive-div-ℕ z x y (pr2 (pr1 H)) d ) ,
  transitive-is-nontrivial-divisors-list-ℕ x y d l (pr2 H)

is-nontrivial-divisors-list-is-decomposition-list-ℕ :
  (x : ℕ) → (l : list ℕ) →
  is-decomposition-list-ℕ x l →
  is-prime-list-ℕ l →
  is-nontrivial-divisors-list-ℕ x l
is-nontrivial-divisors-list-is-decomposition-list-ℕ x nil _ P = star
is-nontrivial-divisors-list-is-decomposition-list-ℕ x (cons y l) H P =
  ( le-one-is-prime-ℕ y (pr1 P)  ,
    ( mul-list-ℕ l) ,
    ( commutative-mul-ℕ (mul-list-ℕ l) y ∙ H)) ,
   transitive-is-nontrivial-divisors-list-ℕ
    ( mul-list-ℕ l)
    ( x)
    ( y , H)
    ( l)
    ( is-nontrivial-divisors-list-is-decomposition-list-ℕ (mul-list-ℕ l) l refl (pr2 P))
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
helper-compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ (succ-ℕ x) H = refl

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

list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → leq-ℕ 1 x → list ℕ
list-fundamental-theorem-arithmetic-ℕ x H =
  map-list nat-Prime-ℕ (list-primes-fundamental-theorem-arithmetic-ℕ x H)

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
            ( λ m →
              mul-ℕ
                ( nat-least-prime-divisor-ℕ
                  ( succ-ℕ n)
                  ( le-succ-leq-ℕ 1 n N))
                ( m))
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
                ( le-succ-leq-ℕ 1 n N))))∙
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

is-nontrivial-divisors-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) →
  is-nontrivial-divisors-list-ℕ x (list-fundamental-theorem-arithmetic-ℕ x H)
is-nontrivial-divisors-list-fundamental-theorem-arithmetic-ℕ x H =
  is-nontrivial-divisors-list-is-decomposition-list-ℕ
    ( x)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
    ( is-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)
    ( is-prime-list-fundamental-theorem-arithmetic-ℕ x H)

is-least-element-list-least-prime-divisor-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (l : list ℕ) →
  is-nontrivial-divisors-list-ℕ
    ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( l) →
  is-least-element-list
    ( ℕ-total-decidable-Poset)
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
      ( pr2 (pr1 D))
      ( div-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))))  ,
  is-least-element-list-least-prime-divisor-ℕ x H l (pr2 D)

is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  is-least-element-list
    ( ℕ-total-decidable-Poset)
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))
is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕ x H =
  is-least-element-list-least-prime-divisor-ℕ
    ( x)
    ( H)
    ( list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))
    ( is-nontrivial-divisors-list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))

is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  is-sorted-least-element-list
    ( ℕ-total-decidable-Poset)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕ x H =
  based-strong-ind-ℕ' 1
    ( λ x H →
      is-sorted-least-element-list
        ( ℕ-total-decidable-Poset)
        ( list-fundamental-theorem-arithmetic-ℕ x H))
    ( raise-star)
    ( λ n N f →
      tr
        ( λ l →
          is-sorted-least-element-list
            ( ℕ-total-decidable-Poset)
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
    ( ℕ-total-decidable-Poset)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
is-sorted-list-fundamental-theorem-arithmetic-ℕ x H =
  is-sorted-list-is-sorted-least-element-list
    ( ℕ-total-decidable-Poset)
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

### The prime decomposition is unique

```agda
prime-decomposition-list-ℕ :
  (x : ℕ) → (leq-ℕ 1 x) → UU lzero
prime-decomposition-list-ℕ x _ =
  Σ (list ℕ) (λ l → is-prime-decomposition-list-ℕ x l)

prime-decomposition-fundamental-theorem-arithmetic-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) → prime-decomposition-list-ℕ x H
pr1 (prime-decomposition-fundamental-theorem-arithmetic-list-ℕ x H) =
  list-fundamental-theorem-arithmetic-ℕ x H
pr2 (prime-decomposition-fundamental-theorem-arithmetic-list-ℕ x H) =
  is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H

le-one-is-non-empty-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  le-ℕ 1 x
le-one-is-non-empty-prime-decomposition-list-ℕ x H y l D =
  concatenate-le-leq-ℕ
    {x = 1}
    {y = y}
    {z = x}
    ( le-one-is-prime-ℕ y (pr1 (pr1 (pr2 D))))
    ( leq-div-ℕ
      ( y)
      ( x)
      ( is-nonzero-leq-one-ℕ x H)
      ( mul-list-ℕ l ,
        ( commutative-mul-ℕ (mul-list-ℕ l) y ∙ pr2 (pr2 D))))

is-divisor-head-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  div-ℕ y x
pr1 (is-divisor-head-prime-decomposition-list-ℕ x H y l D) = mul-list-ℕ l
pr2 (is-divisor-head-prime-decomposition-list-ℕ x H y l D) =
  commutative-mul-ℕ (mul-list-ℕ l) y ∙ pr2 (pr2 D)

is-nontrivial-divisor-head-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  is-nontrivial-divisor-ℕ x y
pr1 (is-nontrivial-divisor-head-prime-decomposition-list-ℕ x H y l D) =
  le-one-is-prime-ℕ y (pr1 (pr1 (pr2 D)))
pr2 (is-nontrivial-divisor-head-prime-decomposition-list-ℕ x H y l D) =
  is-divisor-head-prime-decomposition-list-ℕ x H y l D

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
        ( leq-eq-ℕ x 1 (inv (pr2 (pr2 D)))))
is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕ x H (cons z l) D y d p =
  ind-coprod
    ( λ _ → y ∈-list (cons z l))
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
            ( is-divisor-head-prime-decomposition-list-ℕ x H z l D))
          ( leq-one-quotient-div-ℕ
            ( z)
            ( x)
            ( is-divisor-head-prime-decomposition-list-ℕ x H z l D)
            ( H))
          ( l)
          ( ( is-sorted-tail-is-sorted-list
              ( ℕ-total-decidable-Poset)
              ( cons z l)
              ( pr1 D)) ,
            ( pr2 (pr1 (pr2 D))) ,
            refl)
          ( y)
          {!div-!}
          ( p)))
    ( has-decidable-equality-ℕ y z)

is-lower-bound-head-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  is-lower-bound-ℕ (is-nontrivial-divisor-ℕ x) y
is-lower-bound-head-prime-decomposition-list-ℕ x H y l D m d =
  {!!}

eq-head-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y z : ℕ) (p q : list ℕ ) →
  is-prime-decomposition-list-ℕ x (cons y p) →
  is-prime-decomposition-list-ℕ x (cons z q) →
  y ＝ z
eq-head-prime-decomposition-list-ℕ x H y z p q I J =
  ap
    ( pr1)
    ( all-elements-equal-minimal-element-ℕ
      ( is-nontrivial-divisor-ℕ-Prop x)
      ( y ,
        is-nontrivial-divisor-head-prime-decomposition-list-ℕ x H y p I ,
        is-lower-bound-head-prime-decomposition-list-ℕ x H y p I )
      ( z ,
        is-nontrivial-divisor-head-prime-decomposition-list-ℕ x H z q J ,
        is-lower-bound-head-prime-decomposition-list-ℕ x H z q J))

eq-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (p q : prime-decomposition-list-ℕ x H) →
  p ＝ q
eq-prime-decomposition-list-ℕ x H (nil , _) (nil , _ ) =
  eq-pair-Σ refl (eq-is-prop (is-prop-is-prime-decomposition-list-ℕ x nil))
eq-prime-decomposition-list-ℕ x H (cons y l , I) (nil , J) =
  ex-falso
    ( contradiction-le-ℕ
      ( 1)
      ( x)
      ( le-one-is-non-empty-prime-decomposition-list-ℕ x H y l I)
      ( leq-eq-ℕ x 1 (inv (pr2 (pr2 J)))))
eq-prime-decomposition-list-ℕ x H (nil , I) (cons y l , J) =
  ex-falso
    ( contradiction-le-ℕ
      ( 1)
      ( x)
      ( le-one-is-non-empty-prime-decomposition-list-ℕ x H y l J)
      ( leq-eq-ℕ x 1 (inv (pr2 (pr2 I)))))
eq-prime-decomposition-list-ℕ x H (cons y l , I) (cons z p , J) =
  eq-pair-Σ
    ( eq-Eq-list
      ( cons y l)
      ( cons z p)
      ( ( {!!}) ,
        ( Eq-eq-list
          ( l)
          ( p)
          ( {!!} ∙ {!!}))))
    ( eq-is-prop (is-prop-is-prime-decomposition-list-ℕ x (cons z p)))

is-contr-prime-decomposition-list-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) → is-contr (prime-decomposition-list-ℕ x H)
pr1 (is-contr-prime-decomposition-list-ℕ x H) =
  prime-decomposition-fundamental-theorem-arithmetic-list-ℕ x H
pr2 (is-contr-prime-decomposition-list-ℕ x H) =
  eq-prime-decomposition-list-ℕ
    ( x)
    ( H)
    ( prime-decomposition-fundamental-theorem-arithmetic-list-ℕ x H)
```
