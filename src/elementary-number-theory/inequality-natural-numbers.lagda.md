---
title: Univalent Mathematics in Agda
---

# Inequality of natural numbers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.inequality-natural-numbers where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; commutative-add-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ; commutative-mul-ℕ; right-unit-law-mul-ℕ; right-zero-law-mul-ℕ;
    right-successor-law-mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-zero-ℕ; is-zero-ℕ'; is-nonzero-ℕ;
    is-successor-is-nonzero-ℕ; is-nonzero-succ-ℕ; is-injective-succ-ℕ)
open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (pair)
open import foundation.empty-types using (empty; ex-falso)
open import foundation.functions using (id; _∘_)
open import foundation.functoriality-coproduct-types using (map-coprod)
open import foundation.identity-types using (Id; refl; inv; ap; tr)
open import foundation.negation using (¬)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (UU; lzero)
```

# Inequality on the natural numbers

```agda
leq-ℕ : ℕ → ℕ → UU lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

_≤-ℕ_ = leq-ℕ

data leq-ℕ' : ℕ → ℕ → UU lzero where
  refl-leq-ℕ' : (n : ℕ) → leq-ℕ' n n
  propagate-leq-ℕ' : {x y z : ℕ} → Id (succ-ℕ y) z → (leq-ℕ' x y) → (leq-ℕ' x z) 

-- Some trivialities that will be useful later

leq-zero-ℕ :
  (n : ℕ) → zero-ℕ ≤-ℕ n
leq-zero-ℕ n = star

is-zero-leq-zero-ℕ :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ x
is-zero-leq-zero-ℕ zero-ℕ star = refl

is-zero-leq-zero-ℕ' :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ' x
is-zero-leq-zero-ℕ' zero-ℕ star = refl

succ-leq-ℕ : (n : ℕ) → n ≤-ℕ (succ-ℕ n)
succ-leq-ℕ zero-ℕ = star
succ-leq-ℕ (succ-ℕ n) = succ-leq-ℕ n

concatenate-eq-leq-eq-ℕ :
  {x' x y y' : ℕ} → Id x' x → x ≤-ℕ y → Id y y' → x' ≤-ℕ y'
concatenate-eq-leq-eq-ℕ refl H refl = H

concatenate-leq-eq-ℕ :
  (m : ℕ) {n n' : ℕ} → m ≤-ℕ n → Id n n' → m ≤-ℕ n'
concatenate-leq-eq-ℕ m H refl = H

concatenate-eq-leq-ℕ :
  {m m' : ℕ} (n : ℕ) → Id m' m → m ≤-ℕ n → m' ≤-ℕ n
concatenate-eq-leq-ℕ n refl H = H

is-decidable-leq-ℕ :
  (m n : ℕ) → is-decidable (leq-ℕ m n)
is-decidable-leq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-leq-ℕ m n

decide-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ (succ-ℕ n) → coprod (m ≤-ℕ n) (Id m (succ-ℕ n))
decide-leq-succ-ℕ zero-ℕ zero-ℕ l = inl star
decide-leq-succ-ℕ zero-ℕ (succ-ℕ n) l = inl star
decide-leq-succ-ℕ (succ-ℕ m) zero-ℕ l =
  inr (ap succ-ℕ (is-zero-leq-zero-ℕ m l))
decide-leq-succ-ℕ (succ-ℕ m) (succ-ℕ n) l =
  map-coprod id (ap succ-ℕ) (decide-leq-succ-ℕ m n l)

-- Exercise 6.3 (a)

refl-leq-ℕ : (n : ℕ) → n ≤-ℕ n
refl-leq-ℕ zero-ℕ = star
refl-leq-ℕ (succ-ℕ n) = refl-leq-ℕ n

leq-eq-ℕ : (m n : ℕ) → Id m n → m ≤-ℕ n
leq-eq-ℕ m .m refl = refl-leq-ℕ m

transitive-leq-ℕ :
  (n m l : ℕ) → (n ≤-ℕ m) → (m ≤-ℕ l) → (n ≤-ℕ l)
transitive-leq-ℕ zero-ℕ m l p q = star
transitive-leq-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-leq-ℕ n m l p q

preserves-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ n → m ≤-ℕ (succ-ℕ n)
preserves-leq-succ-ℕ m n p = transitive-leq-ℕ m n (succ-ℕ n) p (succ-leq-ℕ n)

antisymmetric-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → n ≤-ℕ m → Id m n
antisymmetric-leq-ℕ zero-ℕ zero-ℕ p q = refl
antisymmetric-leq-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (antisymmetric-leq-ℕ m n p q)

-- Exercise 6.3 (b)

decide-leq-ℕ :
  (m n : ℕ) → coprod (m ≤-ℕ n) (n ≤-ℕ m)
decide-leq-ℕ zero-ℕ zero-ℕ = inl star
decide-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
decide-leq-ℕ (succ-ℕ m) zero-ℕ = inr star
decide-leq-ℕ (succ-ℕ m) (succ-ℕ n) = decide-leq-ℕ m n

-- Exercise 6.3 (c)

preserves-order-add-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → (add-ℕ m k) ≤-ℕ (add-ℕ n k)
preserves-order-add-ℕ zero-ℕ m n = id
preserves-order-add-ℕ (succ-ℕ k) m n = preserves-order-add-ℕ k m n

reflects-order-add-ℕ :
  (k m n : ℕ) → (add-ℕ m k) ≤-ℕ (add-ℕ n k) → m ≤-ℕ n
reflects-order-add-ℕ zero-ℕ m n = id
reflects-order-add-ℕ (succ-ℕ k) m n = reflects-order-add-ℕ k m n

-- Exercise 6.3 (d)

preserves-order-mul-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → (mul-ℕ m k) ≤-ℕ (mul-ℕ n k)
preserves-order-mul-ℕ k zero-ℕ n p = star
preserves-order-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  preserves-order-add-ℕ k
    ( mul-ℕ m k)
    ( mul-ℕ n k)
    ( preserves-order-mul-ℕ k m n p)

preserves-order-mul-ℕ' :
  (k m n : ℕ) → m ≤-ℕ n → (mul-ℕ k m) ≤-ℕ (mul-ℕ k n)
preserves-order-mul-ℕ' k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-mul-ℕ k m)
    ( preserves-order-mul-ℕ k m n H)
    ( commutative-mul-ℕ n k)

reflects-order-mul-ℕ :
  (k m n : ℕ) → (mul-ℕ m (succ-ℕ k)) ≤-ℕ (mul-ℕ n (succ-ℕ k)) → m ≤-ℕ n
reflects-order-mul-ℕ k zero-ℕ n p = star
reflects-order-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  reflects-order-mul-ℕ k m n
    ( reflects-order-add-ℕ
      ( succ-ℕ k)
      ( mul-ℕ m (succ-ℕ k))
      ( mul-ℕ n (succ-ℕ k))
      ( p))

-- We also record the fact that x ≤-ℕ mul-ℕ x (succ-ℕ k)

leq-mul-ℕ :
  (k x : ℕ) → x ≤-ℕ (mul-ℕ x (succ-ℕ k))
leq-mul-ℕ k x =
  concatenate-eq-leq-ℕ
    ( mul-ℕ x (succ-ℕ k))
    ( inv (right-unit-law-mul-ℕ x))
    ( preserves-order-mul-ℕ' x 1 (succ-ℕ k) (leq-zero-ℕ k))

leq-mul-ℕ' :
  (k x : ℕ) → x ≤-ℕ (mul-ℕ (succ-ℕ k) x)
leq-mul-ℕ' k x =
  concatenate-leq-eq-ℕ x
    ( leq-mul-ℕ k x)
    ( commutative-mul-ℕ x (succ-ℕ k))

leq-mul-is-nonzero-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ (mul-ℕ x k)
leq-mul-is-nonzero-ℕ k x H with is-successor-is-nonzero-ℕ H
... | pair l refl = leq-mul-ℕ l x

leq-mul-is-nonzero-ℕ' :
  (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ (mul-ℕ k x)
leq-mul-is-nonzero-ℕ' k x H with is-successor-is-nonzero-ℕ H
... | pair l refl = leq-mul-ℕ' l x
```

## Min and max on ℕ

```agda
min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ 0 n = 0
min-ℕ (succ-ℕ m) 0 = 0
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)

max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ 0 n = n
max-ℕ (succ-ℕ m) 0 = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)

leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ m → k ≤-ℕ n → k ≤-ℕ (min-ℕ m n)
leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H K = star
leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H K = star
leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H K = star
leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-min-ℕ k m n H K

leq-left-leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ m
leq-left-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
leq-left-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
leq-left-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-left-leq-min-ℕ k m n H

leq-right-leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ n
leq-right-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
leq-right-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
leq-right-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-right-leq-min-ℕ k m n H

leq-max-ℕ :
  (k m n : ℕ) → m ≤-ℕ k → n ≤-ℕ k → (max-ℕ m n) ≤-ℕ k
leq-max-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
leq-max-ℕ (succ-ℕ k) zero-ℕ zero-ℕ H K = star
leq-max-ℕ (succ-ℕ k) zero-ℕ (succ-ℕ n) H K = K
leq-max-ℕ (succ-ℕ k) (succ-ℕ m) zero-ℕ H K = H
leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-max-ℕ k m n H K

leq-left-leq-max-ℕ :
  (k m n : ℕ) → (max-ℕ m n) ≤-ℕ k → m ≤-ℕ k
leq-left-leq-max-ℕ k zero-ℕ zero-ℕ H = star
leq-left-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = star
leq-left-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = H
leq-left-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-left-leq-max-ℕ k m n H

leq-right-leq-max-ℕ :
  (k m n : ℕ) → (max-ℕ m n) ≤-ℕ k → n ≤-ℕ k
leq-right-leq-max-ℕ k zero-ℕ zero-ℕ H = star
leq-right-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = H
leq-right-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = star
leq-right-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-right-leq-max-ℕ k m n H

cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ x y z =
  coprod
    ( coprod ((leq-ℕ x y) × (leq-ℕ y z)) ((leq-ℕ x z) × (leq-ℕ z y)))
    ( coprod
      ( coprod ((leq-ℕ y z) × (leq-ℕ z x)) ((leq-ℕ y x) × (leq-ℕ x z)))
      ( coprod ((leq-ℕ z x) × (leq-ℕ x y)) ((leq-ℕ z y) × (leq-ℕ y x))))

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ = inl (inr (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) =
  inl (map-coprod (pair star) (pair star) (decide-leq-ℕ y z))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ =
  inr (inl (inl (pair star star)))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) =
  inr (inl (map-coprod (pair star) (pair star) (decide-leq-ℕ z x)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ =
  inr (inr (map-coprod (pair star) (pair star) (decide-leq-ℕ x y)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  order-three-elements-ℕ x y z

-- Exercise 6.4

-- The definition of <

le-ℕ : ℕ → ℕ → UU lzero
le-ℕ m zero-ℕ = empty
le-ℕ zero-ℕ (succ-ℕ m) = unit
le-ℕ (succ-ℕ n) (succ-ℕ m) = le-ℕ n m

_<_ = le-ℕ

anti-reflexive-le-ℕ : (n : ℕ) → ¬ (n < n)
anti-reflexive-le-ℕ zero-ℕ ()
anti-reflexive-le-ℕ (succ-ℕ n) = anti-reflexive-le-ℕ n

transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q

succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n

preserves-le-succ-ℕ :
  (m n : ℕ) → le-ℕ m n → le-ℕ m (succ-ℕ n)
preserves-le-succ-ℕ m n H =
  transitive-le-ℕ m n (succ-ℕ n) H (succ-le-ℕ n)

anti-symmetric-le-ℕ : (m n : ℕ) → le-ℕ m n → le-ℕ n m → Id m n
anti-symmetric-le-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (anti-symmetric-le-ℕ m n p q)

is-decidable-le-ℕ :
  (m n : ℕ) → is-decidable (le-ℕ m n)
is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n

contradiction-le-ℕ : (m n : ℕ) → le-ℕ m n → ¬ (n ≤-ℕ m)
contradiction-le-ℕ zero-ℕ (succ-ℕ n) H K = K
contradiction-le-ℕ (succ-ℕ m) (succ-ℕ n) H = contradiction-le-ℕ m n H

contradiction-le-ℕ' : (m n : ℕ) → n ≤-ℕ m → ¬ (le-ℕ m n)
contradiction-le-ℕ' m n K H = contradiction-le-ℕ m n H K

leq-not-le-ℕ : (m n : ℕ) → ¬ (le-ℕ m n) → n ≤-ℕ m
leq-not-le-ℕ zero-ℕ zero-ℕ H = star
leq-not-le-ℕ zero-ℕ (succ-ℕ n) H = ex-falso (H star)
leq-not-le-ℕ (succ-ℕ m) zero-ℕ H = star
leq-not-le-ℕ (succ-ℕ m) (succ-ℕ n) H = leq-not-le-ℕ m n H

is-nonzero-le-ℕ : (m n : ℕ) → le-ℕ m n → is-nonzero-ℕ n
is-nonzero-le-ℕ m n H p = tr (le-ℕ m) p H

contradiction-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → ¬ ((succ-ℕ n) ≤-ℕ m)
contradiction-leq-ℕ (succ-ℕ m) (succ-ℕ n) H K = contradiction-leq-ℕ m n H K

contradiction-leq-ℕ' : (m n : ℕ) → (succ-ℕ n) ≤-ℕ m → ¬ (m ≤-ℕ n)
contradiction-leq-ℕ' m n K H = contradiction-leq-ℕ m n H K

leq-le-ℕ :
  {x y : ℕ} → le-ℕ x y → x ≤-ℕ y
leq-le-ℕ {zero-ℕ} {succ-ℕ y} H = star
leq-le-ℕ {succ-ℕ x} {succ-ℕ y} H = leq-le-ℕ {x} {y} H

concatenate-leq-le-ℕ :
  {x y z : ℕ} → x ≤-ℕ y → le-ℕ y z → le-ℕ x z
concatenate-leq-le-ℕ {zero-ℕ} {zero-ℕ} {succ-ℕ z} H K = star
concatenate-leq-le-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} H K = star
concatenate-leq-le-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} H K =
  concatenate-leq-le-ℕ {x} {y} {z} H K

concatenate-le-leq-ℕ :
  {x y z : ℕ} → le-ℕ x y → y ≤-ℕ z → le-ℕ x z
concatenate-le-leq-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} H K = star
concatenate-le-leq-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} H K =
  concatenate-le-leq-ℕ {x} {y} {z} H K

concatenate-eq-le-eq-ℕ :
  {x y z w : ℕ} → Id x y → le-ℕ y z → Id z w → le-ℕ x w
concatenate-eq-le-eq-ℕ refl p refl = p

concatenate-eq-le-ℕ :
  {x y z : ℕ} → Id x y → le-ℕ y z → le-ℕ x z
concatenate-eq-le-ℕ refl p = p

concatenate-le-eq-ℕ :
  {x y z : ℕ} → le-ℕ x y → Id y z → le-ℕ x z
concatenate-le-eq-ℕ p refl = p

le-succ-ℕ : {x : ℕ} → le-ℕ x (succ-ℕ x)
le-succ-ℕ {zero-ℕ} = star
le-succ-ℕ {succ-ℕ x} = le-succ-ℕ {x}

le-leq-neq-ℕ : {x y : ℕ} → x ≤-ℕ y → ¬ (Id x y) → le-ℕ x y
le-leq-neq-ℕ {zero-ℕ} {zero-ℕ} l f = ex-falso (f refl)
le-leq-neq-ℕ {zero-ℕ} {succ-ℕ y} l f = star
le-leq-neq-ℕ {succ-ℕ x} {succ-ℕ y} l f =
  le-leq-neq-ℕ {x} {y} l (λ p → f (ap succ-ℕ p))

linear-le-ℕ : (x y : ℕ) → coprod (le-ℕ x y) (coprod (Id x y) (le-ℕ y x))
linear-le-ℕ zero-ℕ zero-ℕ = inr (inl refl)
linear-le-ℕ zero-ℕ (succ-ℕ y) = inl star
linear-le-ℕ (succ-ℕ x) zero-ℕ = inr (inr star)
linear-le-ℕ (succ-ℕ x) (succ-ℕ y) =
  map-coprod id (map-coprod (ap succ-ℕ) id) (linear-le-ℕ x y)
```

```agda
left-law-leq-add-ℕ : (k m n : ℕ) → m ≤-ℕ n → (add-ℕ m k) ≤-ℕ (add-ℕ n k)
left-law-leq-add-ℕ zero-ℕ m n = id
left-law-leq-add-ℕ (succ-ℕ k) m n H = left-law-leq-add-ℕ k m n H

right-law-leq-add-ℕ : (k m n : ℕ) → m ≤-ℕ n → (add-ℕ k m) ≤-ℕ (add-ℕ k n) 
right-law-leq-add-ℕ k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-add-ℕ k m)
    ( left-law-leq-add-ℕ k m n H)
    ( commutative-add-ℕ n k)

preserves-leq-add-ℕ :
  {m m' n n' : ℕ} → m ≤-ℕ m' → n ≤-ℕ n' → (add-ℕ m n) ≤-ℕ (add-ℕ m' n')
preserves-leq-add-ℕ {m} {m'} {n} {n'} H K =
  transitive-leq-ℕ
    ( add-ℕ m n)
    ( add-ℕ m' n)
    ( add-ℕ m' n')
    ( left-law-leq-add-ℕ n m m' H)
    ( right-law-leq-add-ℕ m' n n' K)

--------------------------------------------------------------------------------

-- We prove some lemmas about inequalities --

leq-add-ℕ : (m n : ℕ) → m ≤-ℕ (add-ℕ m n)
leq-add-ℕ m zero-ℕ = refl-leq-ℕ m
leq-add-ℕ m (succ-ℕ n) =
  transitive-leq-ℕ m (add-ℕ m n) (succ-ℕ (add-ℕ m n))
    ( leq-add-ℕ m n)
    ( succ-leq-ℕ (add-ℕ m n))

leq-add-ℕ' : (m n : ℕ) → m ≤-ℕ (add-ℕ n m)
leq-add-ℕ' m n =
  concatenate-leq-eq-ℕ m (leq-add-ℕ m n) (commutative-add-ℕ m n)

leq-leq-add-ℕ :
  (m n x : ℕ) → (add-ℕ m x) ≤-ℕ (add-ℕ n x) → m ≤-ℕ n
leq-leq-add-ℕ m n zero-ℕ H = H
leq-leq-add-ℕ m n (succ-ℕ x) H = leq-leq-add-ℕ m n x H

leq-leq-add-ℕ' :
  (m n x : ℕ) → (add-ℕ x m) ≤-ℕ (add-ℕ x n) → m ≤-ℕ n
leq-leq-add-ℕ' m n x H =
  leq-leq-add-ℕ m n x
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-add-ℕ m x)
      ( H)
      ( commutative-add-ℕ x n))

leq-leq-mul-ℕ :
  (m n x : ℕ) → (mul-ℕ (succ-ℕ x) m) ≤-ℕ (mul-ℕ (succ-ℕ x) n) → m ≤-ℕ n
leq-leq-mul-ℕ zero-ℕ zero-ℕ x H = star
leq-leq-mul-ℕ zero-ℕ (succ-ℕ n) x H = star
leq-leq-mul-ℕ (succ-ℕ m) zero-ℕ x H =
  ex-falso
    ( concatenate-leq-eq-ℕ
      ( mul-ℕ (succ-ℕ x) (succ-ℕ m))
      ( H)
      ( right-zero-law-mul-ℕ (succ-ℕ x)))
leq-leq-mul-ℕ (succ-ℕ m) (succ-ℕ n) x H =
  leq-leq-mul-ℕ m n x
    ( leq-leq-add-ℕ' (mul-ℕ (succ-ℕ x) m) (mul-ℕ (succ-ℕ x) n) (succ-ℕ x)
      ( concatenate-eq-leq-eq-ℕ
        ( inv (right-successor-law-mul-ℕ (succ-ℕ x) m))
        ( H)
        ( right-successor-law-mul-ℕ (succ-ℕ x) n)))

leq-leq-mul-ℕ' :
  (m n x : ℕ) → (mul-ℕ m (succ-ℕ x)) ≤-ℕ (mul-ℕ n (succ-ℕ x)) → m ≤-ℕ n
leq-leq-mul-ℕ' m n x H =
  leq-leq-mul-ℕ m n x
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-mul-ℕ (succ-ℕ x) m)
      ( H)
      ( commutative-mul-ℕ n (succ-ℕ x)))
```

```agda
neq-le-ℕ : {x y : ℕ} → le-ℕ x y → ¬ (Id x y)
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H = is-nonzero-succ-ℕ y ∘ inv
neq-le-ℕ {succ-ℕ x} {succ-ℕ y} H p = neq-le-ℕ H (is-injective-succ-ℕ p)
```
