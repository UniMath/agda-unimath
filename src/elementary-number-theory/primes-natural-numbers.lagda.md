---
title: Univalent Mathematics in Agda
---

# Prime numbers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.primes-natural-numbers where

open import foundation.cartesian-product-types using (_×_)
open import foundations.coproduct-types using (inl; inr)
open import foundations.decidable-types using
  ( is-decidable; is-decidable-prod; is-decidable-neg; is-decidable-iff;
    is-decidable-function-type)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import elementary-number-theory.divisibility-natural-numbers using
  ( div-ℕ; div-one-ℕ; leq-div-succ-ℕ; is-zero-is-zero-div-ℕ; is-one-div-ℕ;
    transitive-div-ℕ; is-one-is-divisor-below-ℕ)
open import foundations.empty-type using
  ( ex-falso; is-empty-left-factor-is-empty-prod)
open import elementary-number-theory.equality-natural-numbers using
  ( is-decidable-is-one-ℕ; Eq-eq-ℕ; is-decidable-is-zero-ℕ)
open import elementary-number-theory.factorial-natural-numbers using
  ( factorial-ℕ; div-factorial-ℕ; leq-factorial-ℕ)
open import foundation.functions using (id)
open import foundation.identity-types using (refl; _∙_; inv)
open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; le-ℕ; is-decidable-le-ℕ; is-decidable-leq-ℕ;
    is-zero-leq-zero-ℕ; concatenate-leq-le-ℕ; le-succ-ℕ;
    is-nonzero-le-ℕ; neq-le-ℕ; contradiction-le-ℕ; leq-not-le-ℕ)
open import foundation.levels using (UU; lzero)
open import foundations.logical-equivalence using (_↔_)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( is-decidable-div-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( right-zero-law-mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-one-ℕ; is-not-one-ℕ; is-nonzero-succ-ℕ;
    is-not-one-two-ℕ; is-nonzero-ℕ; is-successor-is-nonzero-ℕ)
open import foundations.negation using (¬)
open import elementary-number-theory.proper-divisors-natural-numbers using
  ( is-proper-divisor-ℕ; is-proper-divisor-zero-succ-ℕ;
    is-decidable-is-proper-divisor-ℕ; le-is-proper-divisor-ℕ)
open import foundations.unit-type using (star)
open import
  elementary-number-theory.well-ordering-principle-natural-numbers using
  ( is-decidable-bounded-Π-ℕ; minimal-element-ℕ; well-ordering-principle-ℕ;
    is-lower-bound-ℕ)
```

# Prime numbers

```agda
is-one-is-proper-divisor-ℕ : ℕ → UU lzero
is-one-is-proper-divisor-ℕ n =
  (x : ℕ) → is-proper-divisor-ℕ n x → is-one-ℕ x

is-prime-ℕ : ℕ → UU lzero
is-prime-ℕ n = (x : ℕ) → (is-proper-divisor-ℕ n x ↔ is-one-ℕ x)

{- Proposition 8.5.2 -}

is-prime-easy-ℕ : ℕ → UU lzero
is-prime-easy-ℕ n = (is-not-one-ℕ n) × (is-one-is-proper-divisor-ℕ n)

is-not-one-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-not-one-ℕ n
is-not-one-is-prime-ℕ n H p = pr1 (pr2 (H 1) refl) (inv p)

is-prime-easy-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-prime-easy-ℕ n
pr1 (is-prime-easy-is-prime-ℕ n H) = is-not-one-is-prime-ℕ n H
pr2 (is-prime-easy-is-prime-ℕ n H) x = pr1 (H x)

is-prime-is-prime-easy-ℕ : (n : ℕ) → is-prime-easy-ℕ n → is-prime-ℕ n
pr1 (is-prime-is-prime-easy-ℕ n H x) = pr2 H x
pr1 (pr2 (is-prime-is-prime-easy-ℕ n H .(succ-ℕ zero-ℕ)) refl) q = pr1 H (inv q)
pr2 (pr2 (is-prime-is-prime-easy-ℕ n H .(succ-ℕ zero-ℕ)) refl) = div-one-ℕ n

is-decidable-is-prime-easy-ℕ : (n : ℕ) → is-decidable (is-prime-easy-ℕ n)
is-decidable-is-prime-easy-ℕ zero-ℕ =
  inr
    ( λ H →
      is-not-one-two-ℕ (pr2 H 2 (is-proper-divisor-zero-succ-ℕ 1)))
is-decidable-is-prime-easy-ℕ (succ-ℕ n) =
  is-decidable-prod
    ( is-decidable-neg (is-decidable-is-one-ℕ (succ-ℕ n)))
    ( is-decidable-bounded-Π-ℕ
      ( is-proper-divisor-ℕ (succ-ℕ n))
      ( is-one-ℕ)
      ( is-decidable-is-proper-divisor-ℕ (succ-ℕ n))
      ( is-decidable-is-one-ℕ)
      ( succ-ℕ n)
      ( λ x H → leq-div-succ-ℕ x n (pr2 H)))

is-decidable-is-prime-ℕ : (n : ℕ) → is-decidable (is-prime-ℕ n)
is-decidable-is-prime-ℕ n =
  is-decidable-iff
    ( is-prime-is-prime-easy-ℕ n)
    ( is-prime-easy-is-prime-ℕ n)
    ( is-decidable-is-prime-easy-ℕ n)

is-one-is-proper-divisor-two-ℕ : is-one-is-proper-divisor-ℕ 2
is-one-is-proper-divisor-two-ℕ zero-ℕ (pair f (pair k p)) =
  ex-falso (f (inv (right-zero-law-mul-ℕ k) ∙ p))
is-one-is-proper-divisor-two-ℕ (succ-ℕ zero-ℕ) (pair f H) = refl
is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) (pair f H) =
  ex-falso (f refl)
is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) (pair f H) =
  ex-falso (leq-div-succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) 1 H)
  
is-prime-easy-two-ℕ : is-prime-easy-ℕ 2
pr1 is-prime-easy-two-ℕ = Eq-eq-ℕ
pr2 is-prime-easy-two-ℕ = is-one-is-proper-divisor-two-ℕ

is-prime-two-ℕ : is-prime-ℕ 2
is-prime-two-ℕ =
  is-prime-is-prime-easy-ℕ 2 is-prime-easy-two-ℕ

{- Definition 8.5.3 -}

in-sieve-of-eratosthenes-ℕ : ℕ → ℕ → UU lzero
in-sieve-of-eratosthenes-ℕ n a =
  (le-ℕ n a) × (is-one-is-divisor-below-ℕ n a)

le-in-sieve-of-eratosthenes-ℕ :
  (n a : ℕ) → in-sieve-of-eratosthenes-ℕ n a → le-ℕ n a
le-in-sieve-of-eratosthenes-ℕ n a = pr1

{- Lemma 8.5.4 -}

is-decidable-in-sieve-of-eratosthenes-ℕ :
  (n a : ℕ) → is-decidable (in-sieve-of-eratosthenes-ℕ n a)
is-decidable-in-sieve-of-eratosthenes-ℕ n a =
  is-decidable-prod
    ( is-decidable-le-ℕ n a)
    ( is-decidable-bounded-Π-ℕ
      ( λ x → leq-ℕ x n)
      ( λ x → div-ℕ x a → is-one-ℕ x)
      ( λ x → is-decidable-leq-ℕ x n)
      ( λ x →
        is-decidable-function-type
          ( is-decidable-div-ℕ x a)
          ( is-decidable-is-one-ℕ x))
      ( n)
      ( λ x → id))

{- Lemma 8.5.5 -}

in-sieve-of-eratosthenes-succ-factorial-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (succ-ℕ (factorial-ℕ n))
pr1 (in-sieve-of-eratosthenes-succ-factorial-ℕ zero-ℕ) = star
pr2 (in-sieve-of-eratosthenes-succ-factorial-ℕ zero-ℕ) x l d =
  ex-falso
    ( Eq-eq-ℕ
      ( is-zero-is-zero-div-ℕ x 2 d (is-zero-leq-zero-ℕ x l)))
pr1 (in-sieve-of-eratosthenes-succ-factorial-ℕ (succ-ℕ n)) =
  concatenate-leq-le-ℕ
    { succ-ℕ n}
    { factorial-ℕ (succ-ℕ n)}
    { succ-ℕ (factorial-ℕ (succ-ℕ n))}
    ( leq-factorial-ℕ (succ-ℕ n))
    ( le-succ-ℕ {factorial-ℕ (succ-ℕ n)})
pr2 (in-sieve-of-eratosthenes-succ-factorial-ℕ (succ-ℕ n)) x l (pair y p) with
  is-decidable-is-zero-ℕ x
... | inl refl =
  ex-falso
    ( is-nonzero-succ-ℕ
      ( factorial-ℕ (succ-ℕ n))
      ( inv p ∙ (right-zero-law-mul-ℕ y)))
... | inr f =
  is-one-div-ℕ x
    ( factorial-ℕ (succ-ℕ n))
    ( div-factorial-ℕ (succ-ℕ n) x l f)
    ( pair y p)

{- Theorem 8.5.6 The infinitude of primes -}

minimal-element-in-sieve-of-eratosthenes-ℕ :
  (n : ℕ) → minimal-element-ℕ (in-sieve-of-eratosthenes-ℕ n)
minimal-element-in-sieve-of-eratosthenes-ℕ n =
  well-ordering-principle-ℕ
    ( in-sieve-of-eratosthenes-ℕ n)
    ( is-decidable-in-sieve-of-eratosthenes-ℕ n)
    ( pair
      ( succ-ℕ (factorial-ℕ n))
      ( in-sieve-of-eratosthenes-succ-factorial-ℕ n))

larger-prime-ℕ : ℕ → ℕ
larger-prime-ℕ n = pr1 (minimal-element-in-sieve-of-eratosthenes-ℕ n)

in-sieve-of-eratosthenes-larger-prime-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (larger-prime-ℕ n)
in-sieve-of-eratosthenes-larger-prime-ℕ n =
  pr1 (pr2 (minimal-element-in-sieve-of-eratosthenes-ℕ n))

is-one-is-divisor-below-larger-prime-ℕ :
  (n : ℕ) → is-one-is-divisor-below-ℕ n (larger-prime-ℕ n)
is-one-is-divisor-below-larger-prime-ℕ n =
  pr2 (in-sieve-of-eratosthenes-larger-prime-ℕ n)

le-larger-prime-ℕ : (n : ℕ) → le-ℕ n (larger-prime-ℕ n)
le-larger-prime-ℕ n = pr1 (in-sieve-of-eratosthenes-larger-prime-ℕ n)

is-nonzero-larger-prime-ℕ : (n : ℕ) → is-nonzero-ℕ (larger-prime-ℕ n)
is-nonzero-larger-prime-ℕ n =
  is-nonzero-le-ℕ n (larger-prime-ℕ n) (le-larger-prime-ℕ n)

is-lower-bound-larger-prime-ℕ :
  (n : ℕ) → is-lower-bound-ℕ (in-sieve-of-eratosthenes-ℕ n) (larger-prime-ℕ n)
is-lower-bound-larger-prime-ℕ n =
  pr2 (pr2 (minimal-element-in-sieve-of-eratosthenes-ℕ n))

is-not-one-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-not-one-ℕ (larger-prime-ℕ n)
is-not-one-larger-prime-ℕ n H p with is-successor-is-nonzero-ℕ H
... | pair k refl =
  neq-le-ℕ {1} {larger-prime-ℕ n}
    ( concatenate-leq-le-ℕ {1} {succ-ℕ k} {larger-prime-ℕ n} star
      ( le-larger-prime-ℕ (succ-ℕ k)))
    ( inv p)

not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ :
  (n x : ℕ) → is-proper-divisor-ℕ (larger-prime-ℕ n) x →
  ¬ (in-sieve-of-eratosthenes-ℕ n x)
not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x H K =
  ex-falso
    ( contradiction-le-ℕ x (larger-prime-ℕ n)
      ( le-is-proper-divisor-ℕ x (larger-prime-ℕ n)
        ( is-nonzero-larger-prime-ℕ n)
        ( H))
      ( is-lower-bound-larger-prime-ℕ n x K))

is-one-is-proper-divisor-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-one-is-proper-divisor-ℕ (larger-prime-ℕ n)
is-one-is-proper-divisor-larger-prime-ℕ n H x (pair f K) =
  is-one-is-divisor-below-larger-prime-ℕ n x
    ( leq-not-le-ℕ n x
      ( is-empty-left-factor-is-empty-prod
        ( not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x
          ( pair f K))
        ( λ y l d →
          is-one-is-divisor-below-larger-prime-ℕ n y l
            ( transitive-div-ℕ y x (larger-prime-ℕ n) d K))))
    ( K)

is-prime-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-prime-ℕ (larger-prime-ℕ n)
is-prime-larger-prime-ℕ n H =
  is-prime-is-prime-easy-ℕ
    ( larger-prime-ℕ n)
    ( pair
      ( is-not-one-larger-prime-ℕ n H)
      ( is-one-is-proper-divisor-larger-prime-ℕ n H))

infinitude-of-primes-ℕ :
  (n : ℕ) → Σ ℕ (λ p → is-prime-ℕ p × le-ℕ n p)
infinitude-of-primes-ℕ n with is-decidable-is-zero-ℕ n
... | inl refl = pair 2 (pair is-prime-two-ℕ star)
... | inr H =
  pair
    ( larger-prime-ℕ n)
    ( pair
      ( is-prime-larger-prime-ℕ n H)
      ( le-larger-prime-ℕ n))
```

```agda
prime-ℕ : ℕ → ℕ
prime-ℕ zero-ℕ = 2
prime-ℕ (succ-ℕ n) = pr1 (infinitude-of-primes-ℕ (prime-ℕ n))

prime-counting-ℕ : ℕ → ℕ
prime-counting-ℕ zero-ℕ = zero-ℕ
prime-counting-ℕ (succ-ℕ n) with is-decidable-is-prime-ℕ (succ-ℕ n)
... | inl x = succ-ℕ (prime-counting-ℕ n)
... | inr x = prime-counting-ℕ n
```
