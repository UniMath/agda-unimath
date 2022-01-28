---
title: Univalent Mathematics in Agda
---

# The natural numbers base k

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.finitary-natural-numbers where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; left-unit-law-add-ℕ; is-injective-add-ℕ'; commutative-add-ℕ)
open import elementary-number-theory.congruence-natural-numbers using
  ( cong-ℕ; concatenate-cong-eq-ℕ; translation-invariant-cong-ℕ';
    eq-cong-le-ℕ; concatenate-cong-eq-cong-ℕ; symm-cong-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( le-ℕ; concatenate-le-leq-ℕ; transitive-leq-ℕ; leq-mul-ℕ; leq-add-ℕ;
    neq-le-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ; commutative-mul-ℕ; is-injective-mul-succ-ℕ; right-unit-law-mul-ℕ;
    right-successor-law-mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-injective-succ-ℕ)
open import elementary-number-theory.standard-finite-types using
  ( Fin; nat-Fin; strict-upper-bound-nat-Fin; is-injective-nat-Fin; zero-Fin;
    succ-Fin; nat-succ-Fin; is-zero-nat-zero-Fin)
open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (pair)
open import foundation.empty-types using (is-empty; ex-falso)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap)
open import foundation.injective-maps using (is-injective)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (UU; lzero)
```

# The finitary natural numbers

```agda
data based-ℕ : ℕ → UU lzero where
  constant-based-ℕ : (k : ℕ) → Fin k → based-ℕ k
  unary-op-based-ℕ : (k : ℕ) → Fin k → based-ℕ k → based-ℕ k

{- Converting a k-ary natural number to a natural number -}

constant-ℕ : (k : ℕ) → Fin k → ℕ
constant-ℕ k x = nat-Fin x

unary-op-ℕ : (k : ℕ) → Fin k → ℕ → ℕ
unary-op-ℕ k x n = add-ℕ (mul-ℕ k (succ-ℕ n)) (nat-Fin x)

convert-based-ℕ : (k : ℕ) → based-ℕ k → ℕ
convert-based-ℕ k (constant-based-ℕ .k x) =
  constant-ℕ k x
convert-based-ℕ k (unary-op-based-ℕ .k x n) =
  unary-op-ℕ k x (convert-based-ℕ k n)

-- Exercise 7.10 (a)

{- The type of 0-ary natural numbers is empty -}
is-empty-based-zero-ℕ : is-empty (based-ℕ zero-ℕ)
is-empty-based-zero-ℕ (constant-based-ℕ .zero-ℕ ())
is-empty-based-zero-ℕ (unary-op-based-ℕ .zero-ℕ () n)

-- Exercise 7.10 (b)

{- We show that the function convert-based-ℕ is injective -}

cong-unary-op-ℕ :
  (k : ℕ) (x : Fin k) (n : ℕ) →
  cong-ℕ k (unary-op-ℕ k x n) (nat-Fin x)
cong-unary-op-ℕ (succ-ℕ k) x n =
  concatenate-cong-eq-ℕ
    ( succ-ℕ k)
    { unary-op-ℕ (succ-ℕ k) x n}
    ( translation-invariant-cong-ℕ'
      ( succ-ℕ k)
      ( mul-ℕ (succ-ℕ k) (succ-ℕ n))
      ( zero-ℕ)
      ( nat-Fin x)
      ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (succ-ℕ k))))
    ( left-unit-law-add-ℕ (nat-Fin x))

{- Any natural number of the form constant-ℕ k x is strictly less than any
   natural number of the form unary-op-ℕ k y m -}

le-constant-unary-op-ℕ :
  (k : ℕ) (x y : Fin k) (m : ℕ) → le-ℕ (constant-ℕ k x) (unary-op-ℕ k y m)
le-constant-unary-op-ℕ k x y m =
  concatenate-le-leq-ℕ {nat-Fin x} {k} {unary-op-ℕ k y m}
    ( strict-upper-bound-nat-Fin x)
    ( transitive-leq-ℕ
      ( k)
      ( mul-ℕ k (succ-ℕ m))
      ( unary-op-ℕ k y m)
        ( leq-mul-ℕ m k)
        ( leq-add-ℕ (mul-ℕ k (succ-ℕ m)) (nat-Fin y)))

is-injective-convert-based-ℕ :
  (k : ℕ) → is-injective (convert-based-ℕ k)
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { constant-based-ℕ .(succ-ℕ k) x}
  { constant-based-ℕ .(succ-ℕ k) y} p =
  ap (constant-based-ℕ (succ-ℕ k)) (is-injective-nat-Fin p)
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { constant-based-ℕ .(succ-ℕ k) x}
  { unary-op-based-ℕ .(succ-ℕ k) y m} p =
  ex-falso
    ( neq-le-ℕ
      ( le-constant-unary-op-ℕ (succ-ℕ k) x y (convert-based-ℕ (succ-ℕ k) m))
      ( p))
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { unary-op-based-ℕ .(succ-ℕ k) x n}
  { constant-based-ℕ .(succ-ℕ k) y} p =
  ex-falso
    ( neq-le-ℕ
      ( le-constant-unary-op-ℕ (succ-ℕ k) y x (convert-based-ℕ (succ-ℕ k) n))
      ( inv p))
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { unary-op-based-ℕ .(succ-ℕ k) x n}
  { unary-op-based-ℕ .(succ-ℕ k) y m} p with
  -- the following term has type Id x y
  is-injective-nat-Fin {succ-ℕ k} {x} {y}
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin x)
      ( nat-Fin y)
      ( strict-upper-bound-nat-Fin x)
      ( strict-upper-bound-nat-Fin y)
      ( concatenate-cong-eq-cong-ℕ
        { succ-ℕ k}
        { nat-Fin x}
        { unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n)}
        { unary-op-ℕ (succ-ℕ k) y (convert-based-ℕ (succ-ℕ k) m)}
        { nat-Fin y}
        ( symm-cong-ℕ
          ( succ-ℕ k)
          ( unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n))
          ( nat-Fin x)
          ( cong-unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n)))
        ( p)
        ( cong-unary-op-ℕ (succ-ℕ k) y (convert-based-ℕ (succ-ℕ k) m))))
... | refl =
  ap ( unary-op-based-ℕ (succ-ℕ k) x)
     ( is-injective-convert-based-ℕ (succ-ℕ k)
       ( is-injective-succ-ℕ
         ( is-injective-mul-succ-ℕ k
           ( is-injective-add-ℕ' (nat-Fin x) p))))

-- Exercise 7.10 (c)

{- We show that the map convert-based-ℕ has an inverse. -}

-- The zero-element of the (k+1)-ary natural numbers
zero-based-ℕ : (k : ℕ) → based-ℕ (succ-ℕ k)
zero-based-ℕ k = constant-based-ℕ (succ-ℕ k) zero-Fin

-- The successor function on the k-ary natural numbers
succ-based-ℕ : (k : ℕ) → based-ℕ k → based-ℕ k
succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inl x)) =
  constant-based-ℕ (succ-ℕ k) (succ-Fin (inl x))
succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inr star)) =
  unary-op-based-ℕ (succ-ℕ k) zero-Fin (constant-based-ℕ (succ-ℕ k) zero-Fin)
succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inl x) n) =
  unary-op-based-ℕ (succ-ℕ k) (succ-Fin (inl x)) n
succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inr x) n) =
  unary-op-based-ℕ (succ-ℕ k) zero-Fin (succ-based-ℕ (succ-ℕ k) n)

-- The inverse map of convert-based-ℕ
inv-convert-based-ℕ : (k : ℕ) → ℕ → based-ℕ (succ-ℕ k)
inv-convert-based-ℕ k zero-ℕ =
  zero-based-ℕ k
inv-convert-based-ℕ k (succ-ℕ n) =
  succ-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ k n)

convert-based-succ-based-ℕ :
  (k : ℕ) (x : based-ℕ k) →
  Id (convert-based-ℕ k (succ-based-ℕ k x)) (succ-ℕ (convert-based-ℕ k x))
convert-based-succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inl x)) =
  nat-succ-Fin x
convert-based-succ-based-ℕ
  ( succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inr star)) =
  ( ap
    ( λ t → add-ℕ (mul-ℕ (succ-ℕ k) (succ-ℕ t)) t)
    ( is-zero-nat-zero-Fin {k})) ∙
  ( right-unit-law-mul-ℕ (succ-ℕ k))
convert-based-succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inl x) n) =
  ap ( add-ℕ (mul-ℕ (succ-ℕ k) (succ-ℕ (convert-based-ℕ (succ-ℕ k) n))))
     ( nat-succ-Fin {k} x)
convert-based-succ-based-ℕ
  (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inr star) n) =
  ( ap ( add-ℕ
         ( mul-ℕ
           ( succ-ℕ k)
           ( succ-ℕ (convert-based-ℕ (succ-ℕ k) (succ-based-ℕ (succ-ℕ k) n)))))
       ( is-zero-nat-zero-Fin {k})) ∙
  ( ( ap ( (mul-ℕ (succ-ℕ k)) ∘ succ-ℕ)
         ( convert-based-succ-based-ℕ (succ-ℕ k) n)) ∙
    ( ( right-successor-law-mul-ℕ
        ( succ-ℕ k)
        ( succ-ℕ (convert-based-ℕ (succ-ℕ k) n))) ∙
      ( commutative-add-ℕ
        ( succ-ℕ k)
        ( mul-ℕ (succ-ℕ k) (succ-ℕ (convert-based-ℕ (succ-ℕ k) n))))))

issec-inv-convert-based-ℕ :
  (k n : ℕ) → Id (convert-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ k n)) n
issec-inv-convert-based-ℕ k zero-ℕ = is-zero-nat-zero-Fin {k}
issec-inv-convert-based-ℕ k (succ-ℕ n) =
  ( convert-based-succ-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ  k n)) ∙
  ( ap succ-ℕ (issec-inv-convert-based-ℕ k n))

isretr-inv-convert-based-ℕ :
  (k : ℕ) (x : based-ℕ (succ-ℕ k)) →
  Id (inv-convert-based-ℕ k (convert-based-ℕ (succ-ℕ k) x)) x
isretr-inv-convert-based-ℕ k x =
  is-injective-convert-based-ℕ
    ( succ-ℕ k)
    ( issec-inv-convert-based-ℕ k (convert-based-ℕ (succ-ℕ k) x))
```
