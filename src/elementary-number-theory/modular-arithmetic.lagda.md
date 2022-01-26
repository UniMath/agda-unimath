---
title: Univalent Mathematics in Agda
---

# Modular arithmetic

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.modular-arithmetic where

open import elementary-number-theory.addition-integers using
  ( add-ℤ; ap-add-ℤ; is-injective-add-ℤ; is-injective-add-ℤ'; associative-add-ℤ;
    commutative-add-ℤ; left-unit-law-add-ℤ; right-unit-law-add-ℤ;
    left-inverse-law-add-ℤ; right-inverse-law-add-ℤ;
    left-successor-law-add-ℤ; right-successor-law-add-ℤ;
    left-predecessor-law-add-ℤ; right-predecessor-law-add-ℤ;
    is-add-one-succ-ℤ; is-add-one-succ-ℤ'; is-add-neg-one-pred-ℤ;
    is-add-neg-one-pred-ℤ'; is-equiv-add-ℤ; is-equiv-add-ℤ')
open import elementary-number-theory.congruence-integers using
  ( cong-ℤ; refl-cong-ℤ; cong-int-cong-ℕ; concatenate-eq-cong-ℤ;
    transitive-cong-ℤ; concatenate-cong-eq-cong-ℤ; symmetric-cong-ℤ;
    is-discrete-cong-ℤ; cong-cong-int-ℕ; concatenate-cong-cong-cong-ℤ;
    is-cong-zero-div-ℤ; div-is-cong-zero-ℤ; is-unit-cong-succ-ℤ)
open import elementary-number-theory.congruence-natural-numbers using
  ( refl-cong-ℕ; congruence-mul-ℕ; eq-cong-nat-Fin)
open import foundations.coproduct-types using (inl; inr)
open import foundations.decidable-equality using (has-decidable-equality)
open import foundations.dependent-pair-types using (pair; pr1; pr2)
open import elementary-number-theory.divisibility-integers using
  ( div-ℤ; is-zero-div-zero-ℤ; refl-div-ℤ; is-one-is-unit-int-ℕ)
open import elementary-number-theory.equality-integers using
  ( has-decidable-equality-ℤ)
open import elementary-number-theory.equality-standard-finite-types using
  ( has-decidable-equality-Fin)
open import foundations.equivalences using (is-equiv; _≃_)
open import foundations.identity-types using (Id; refl; _∙_; inv; ap; ap-binary)
open import foundations.injective-maps using
  ( is-injective; is-injective-id; is-injective-comp')
open import elementary-number-theory.integers using
  ( ℤ; zero-ℤ; neg-one-ℤ; one-ℤ; int-ℕ; is-injective-int-ℕ; is-zero-ℤ; succ-ℤ;
    pred-ℤ; issec-pred-ℤ; isretr-pred-ℤ; neg-ℤ; succ-int-ℕ; is-equiv-succ-ℤ;
    is-equiv-pred-ℤ; is-equiv-neg-ℤ)
open import foundations.levels using (UU; lzero)
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; mul-ℤ'; associative-mul-ℤ; commutative-mul-ℤ; left-zero-law-mul-ℤ;
    right-zero-law-mul-ℤ; left-unit-law-mul-ℤ; right-unit-law-mul-ℤ;
    left-distributive-mul-add-ℤ; right-distributive-mul-add-ℤ;
    is-mul-neg-one-neg-ℤ; is-mul-neg-one-neg-ℤ'; mul-int-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-one-ℕ; is-not-one-ℕ)
open import foundations.negation using (¬; functor-neg)
open import elementary-number-theory.standard-finite-types using
  ( Fin; zero-Fin; neg-one-Fin; one-Fin; nat-Fin; is-injective-nat-Fin;
    is-zero-nat-zero-Fin; succ-Fin; pred-Fin; issec-pred-Fin; isretr-pred-Fin;
    is-equiv-succ-Fin; is-equiv-pred-Fin)
open import foundations.unit-type using (star)
```

Some modular arithmetic was already defined in `modular-arithmetic-standard-finite-types`. Here we package those results together in a more convenient package that also allows congruence modulo 0.

```agda
ℤ-Mod : ℕ → UU lzero
ℤ-Mod zero-ℕ = ℤ
ℤ-Mod (succ-ℕ k) = Fin (succ-ℕ k)
```

## Important integers modulo k

```agda
zero-ℤ-Mod : (k : ℕ) → ℤ-Mod k
zero-ℤ-Mod zero-ℕ = zero-ℤ
zero-ℤ-Mod (succ-ℕ k) = zero-Fin

is-zero-ℤ-Mod : (k : ℕ) → ℤ-Mod k → UU lzero
is-zero-ℤ-Mod k x = Id x (zero-ℤ-Mod k)

is-nonzero-ℤ-Mod : (k : ℕ) → ℤ-Mod k → UU lzero
is-nonzero-ℤ-Mod k x = ¬ (is-zero-ℤ-Mod k x)

neg-one-ℤ-Mod : (k : ℕ) → ℤ-Mod k
neg-one-ℤ-Mod zero-ℕ = neg-one-ℤ
neg-one-ℤ-Mod (succ-ℕ k) = neg-one-Fin

one-ℤ-Mod : (k : ℕ) → ℤ-Mod k
one-ℤ-Mod zero-ℕ = one-ℤ
one-ℤ-Mod (succ-ℕ k) = one-Fin
```

## The integers modulo k have decidable equality

```agda
has-decidable-equality-ℤ-Mod : (k : ℕ) → has-decidable-equality (ℤ-Mod k)
has-decidable-equality-ℤ-Mod zero-ℕ = has-decidable-equality-ℤ
has-decidable-equality-ℤ-Mod (succ-ℕ k) = has-decidable-equality-Fin
```

## The inclusion of the integers modulo k into ℤ

```agda
int-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ
int-ℤ-Mod zero-ℕ x = x
int-ℤ-Mod (succ-ℕ k) x = int-ℕ (nat-Fin x)

is-injective-int-ℤ-Mod : (k : ℕ) → is-injective (int-ℤ-Mod k)
is-injective-int-ℤ-Mod zero-ℕ = is-injective-id
is-injective-int-ℤ-Mod (succ-ℕ k) =
  is-injective-comp' is-injective-nat-Fin is-injective-int-ℕ

is-zero-int-zero-ℤ-Mod : (k : ℕ) → is-zero-ℤ (int-ℤ-Mod k (zero-ℤ-Mod k))
is-zero-int-zero-ℤ-Mod (zero-ℕ) = refl
is-zero-int-zero-ℤ-Mod (succ-ℕ k) = ap int-ℕ (is-zero-nat-zero-Fin {k})
```

## The successor and predecessor functions on the integers modulo k

```agda
succ-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k
succ-ℤ-Mod zero-ℕ = succ-ℤ
succ-ℤ-Mod (succ-ℕ k) = succ-Fin

abstract
  is-equiv-succ-ℤ-Mod : (k : ℕ) → is-equiv (succ-ℤ-Mod k)
  is-equiv-succ-ℤ-Mod zero-ℕ = is-equiv-succ-ℤ
  is-equiv-succ-ℤ-Mod (succ-ℕ k) = is-equiv-succ-Fin

equiv-succ-ℤ-Mod : (k : ℕ) → ℤ-Mod k ≃ ℤ-Mod k
pr1 (equiv-succ-ℤ-Mod k) = succ-ℤ-Mod k
pr2 (equiv-succ-ℤ-Mod k) = is-equiv-succ-ℤ-Mod k

pred-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k
pred-ℤ-Mod zero-ℕ = pred-ℤ
pred-ℤ-Mod (succ-ℕ k) = pred-Fin

issec-pred-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → Id (succ-ℤ-Mod k (pred-ℤ-Mod k x)) x
issec-pred-ℤ-Mod zero-ℕ = issec-pred-ℤ
issec-pred-ℤ-Mod (succ-ℕ k) = issec-pred-Fin

isretr-pred-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → Id (pred-ℤ-Mod k (succ-ℤ-Mod k x)) x
isretr-pred-ℤ-Mod zero-ℕ = isretr-pred-ℤ
isretr-pred-ℤ-Mod (succ-ℕ k) = isretr-pred-Fin

abstract
  is-equiv-pred-ℤ-Mod : (k : ℕ) → is-equiv (pred-ℤ-Mod k)
  is-equiv-pred-ℤ-Mod zero-ℕ = is-equiv-pred-ℤ
  is-equiv-pred-ℤ-Mod (succ-ℕ k) = is-equiv-pred-Fin

equiv-pred-ℤ-Mod : (k : ℕ) → ℤ-Mod k ≃ ℤ-Mod k
pr1 (equiv-pred-ℤ-Mod k) = pred-ℤ-Mod k
pr2 (equiv-pred-ℤ-Mod k) = is-equiv-pred-ℤ-Mod k
```

## Addition on the integers modulo k

```
add-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
add-ℤ-Mod zero-ℕ = add-ℤ
add-ℤ-Mod (succ-ℕ k) = add-Fin

add-ℤ-Mod' : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
add-ℤ-Mod' k x y = add-ℤ-Mod k y x

ap-add-ℤ-Mod :
  (k : ℕ) {x x' y y' : ℤ-Mod k} →
  Id x x' → Id y y' → Id (add-ℤ-Mod k x y) (add-ℤ-Mod k x' y')
ap-add-ℤ-Mod k p q = ap-binary (add-ℤ-Mod k) p q

abstract
  is-equiv-add-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → is-equiv (add-ℤ-Mod k x)
  is-equiv-add-ℤ-Mod zero-ℕ = is-equiv-add-ℤ
  is-equiv-add-ℤ-Mod (succ-ℕ k) = is-equiv-add-Fin

equiv-add-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → ℤ-Mod k ≃ ℤ-Mod k
pr1 (equiv-add-ℤ-Mod k x) = add-ℤ-Mod k x
pr2 (equiv-add-ℤ-Mod k x) = is-equiv-add-ℤ-Mod k x

abstract
  is-equiv-add-ℤ-Mod' : (k : ℕ) (x : ℤ-Mod k) → is-equiv (add-ℤ-Mod' k x)
  is-equiv-add-ℤ-Mod' zero-ℕ = is-equiv-add-ℤ'
  is-equiv-add-ℤ-Mod' (succ-ℕ k) = is-equiv-add-Fin'

equiv-add-ℤ-Mod' : (k : ℕ) (x : ℤ-Mod k) → ℤ-Mod k ≃ ℤ-Mod k
pr1 (equiv-add-ℤ-Mod' k x) = add-ℤ-Mod' k x
pr2 (equiv-add-ℤ-Mod' k x) = is-equiv-add-ℤ-Mod' k x

is-injective-add-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → is-injective (add-ℤ-Mod k x)
is-injective-add-ℤ-Mod zero-ℕ = is-injective-add-ℤ
is-injective-add-ℤ-Mod (succ-ℕ k) = is-injective-add-Fin

is-injective-add-ℤ-Mod' : (k : ℕ) (x : ℤ-Mod k) → is-injective (add-ℤ-Mod' k x)
is-injective-add-ℤ-Mod' zero-ℕ = is-injective-add-ℤ'
is-injective-add-ℤ-Mod' (succ-ℕ k) = is-injective-add-Fin'
```

## The negative of an integer modulo k

```agda
neg-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k
neg-ℤ-Mod zero-ℕ = neg-ℤ
neg-ℤ-Mod (succ-ℕ k) = neg-Fin

abstract
  is-equiv-neg-ℤ-Mod : (k : ℕ) → is-equiv (neg-ℤ-Mod k)
  is-equiv-neg-ℤ-Mod zero-ℕ = is-equiv-neg-ℤ
  is-equiv-neg-ℤ-Mod (succ-ℕ k) = is-equiv-neg-Fin

equiv-neg-ℤ-Mod : (k : ℕ) → ℤ-Mod k ≃ ℤ-Mod k
pr1 (equiv-neg-ℤ-Mod k) = neg-ℤ-Mod k
pr2 (equiv-neg-ℤ-Mod k) = is-equiv-neg-ℤ-Mod k
```

## Laws of addition modulo k

```agda
associative-add-ℤ-Mod :
  (k : ℕ) (x y z : ℤ-Mod k) →
  Id (add-ℤ-Mod k (add-ℤ-Mod k x y) z) (add-ℤ-Mod k x (add-ℤ-Mod k y z))
associative-add-ℤ-Mod zero-ℕ = associative-add-ℤ
associative-add-ℤ-Mod (succ-ℕ k) = associative-add-Fin

commutative-add-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) → Id (add-ℤ-Mod k x y) (add-ℤ-Mod k y x)
commutative-add-ℤ-Mod zero-ℕ = commutative-add-ℤ
commutative-add-ℤ-Mod (succ-ℕ k) = commutative-add-Fin

left-unit-law-add-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → Id (add-ℤ-Mod k (zero-ℤ-Mod k) x) x
left-unit-law-add-ℤ-Mod zero-ℕ = left-unit-law-add-ℤ
left-unit-law-add-ℤ-Mod (succ-ℕ k) = left-unit-law-add-Fin

right-unit-law-add-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → Id (add-ℤ-Mod k x (zero-ℤ-Mod k)) x
right-unit-law-add-ℤ-Mod zero-ℕ = right-unit-law-add-ℤ
right-unit-law-add-ℤ-Mod (succ-ℕ k) = right-unit-law-add-Fin

left-inverse-law-add-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → Id (add-ℤ-Mod k (neg-ℤ-Mod k x) x) (zero-ℤ-Mod k)
left-inverse-law-add-ℤ-Mod zero-ℕ = left-inverse-law-add-ℤ
left-inverse-law-add-ℤ-Mod (succ-ℕ k) = left-inverse-law-add-Fin

right-inverse-law-add-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → Id (add-ℤ-Mod k x (neg-ℤ-Mod k x)) (zero-ℤ-Mod k)
right-inverse-law-add-ℤ-Mod zero-ℕ = right-inverse-law-add-ℤ
right-inverse-law-add-ℤ-Mod (succ-ℕ k) = right-inverse-law-add-Fin

left-successor-law-add-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) →
  Id (add-ℤ-Mod k (succ-ℤ-Mod k x) y) (succ-ℤ-Mod k (add-ℤ-Mod k x y))
left-successor-law-add-ℤ-Mod zero-ℕ = left-successor-law-add-ℤ
left-successor-law-add-ℤ-Mod (succ-ℕ k) = left-successor-law-add-Fin

right-successor-law-add-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) →
  Id (add-ℤ-Mod k x (succ-ℤ-Mod k y)) (succ-ℤ-Mod k (add-ℤ-Mod k x y))
right-successor-law-add-ℤ-Mod zero-ℕ = right-successor-law-add-ℤ
right-successor-law-add-ℤ-Mod (succ-ℕ k) = right-successor-law-add-Fin

left-predecessor-law-add-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) →
  Id (add-ℤ-Mod k (pred-ℤ-Mod k x) y) (pred-ℤ-Mod k (add-ℤ-Mod k x y))
left-predecessor-law-add-ℤ-Mod zero-ℕ = left-predecessor-law-add-ℤ
left-predecessor-law-add-ℤ-Mod (succ-ℕ k) = left-predecessor-law-add-Fin

right-predecessor-law-add-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) →
  Id (add-ℤ-Mod k x (pred-ℤ-Mod k y)) (pred-ℤ-Mod k (add-ℤ-Mod k x y))
right-predecessor-law-add-ℤ-Mod zero-ℕ = right-predecessor-law-add-ℤ
right-predecessor-law-add-ℤ-Mod (succ-ℕ k) = right-predecessor-law-add-Fin

is-add-one-succ-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → Id (succ-ℤ-Mod k x) (add-ℤ-Mod k (one-ℤ-Mod k) x)
is-add-one-succ-ℤ-Mod zero-ℕ = is-add-one-succ-ℤ
is-add-one-succ-ℤ-Mod (succ-ℕ k) = is-add-one-succ-Fin

is-add-one-succ-ℤ-Mod' :
  (k : ℕ) (x : ℤ-Mod k) → Id (succ-ℤ-Mod k x) (add-ℤ-Mod k x (one-ℤ-Mod k))
is-add-one-succ-ℤ-Mod' zero-ℕ = is-add-one-succ-ℤ'
is-add-one-succ-ℤ-Mod' (succ-ℕ k) = is-add-one-succ-Fin'

is-add-neg-one-pred-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → Id (pred-ℤ-Mod k x) (add-ℤ-Mod k (neg-one-ℤ-Mod k) x)
is-add-neg-one-pred-ℤ-Mod zero-ℕ = is-add-neg-one-pred-ℤ
is-add-neg-one-pred-ℤ-Mod (succ-ℕ k) = is-add-neg-one-pred-Fin

is-add-neg-one-pred-ℤ-Mod' :
  (k : ℕ) (x : ℤ-Mod k) → Id (pred-ℤ-Mod k x) (add-ℤ-Mod k x (neg-one-ℤ-Mod k))
is-add-neg-one-pred-ℤ-Mod' zero-ℕ = is-add-neg-one-pred-ℤ'
is-add-neg-one-pred-ℤ-Mod' (succ-ℕ k) = is-add-neg-one-pred-Fin'
```

## Multiplication modulo k

```agda
mul-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
mul-ℤ-Mod zero-ℕ = mul-ℤ
mul-ℤ-Mod (succ-ℕ k) = mul-Fin

mul-ℤ-Mod' : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
mul-ℤ-Mod' k x y = mul-ℤ-Mod k y x

ap-mul-ℤ-Mod :
  (k : ℕ) {x x' y y' : ℤ-Mod k} →
  Id x x' → Id y y' → Id (mul-ℤ-Mod k x y) (mul-ℤ-Mod k x' y')
ap-mul-ℤ-Mod k p q = ap-binary (mul-ℤ-Mod k) p q
```

## Laws of multiplication modulo k

```agda
associative-mul-ℤ-Mod :
  (k : ℕ) (x y z : ℤ-Mod k) →
  Id (mul-ℤ-Mod k (mul-ℤ-Mod k x y) z) (mul-ℤ-Mod k x (mul-ℤ-Mod k y z))
associative-mul-ℤ-Mod zero-ℕ = associative-mul-ℤ
associative-mul-ℤ-Mod (succ-ℕ k) = associative-mul-Fin

commutative-mul-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) → Id (mul-ℤ-Mod k x y) (mul-ℤ-Mod k y x)
commutative-mul-ℤ-Mod zero-ℕ = commutative-mul-ℤ
commutative-mul-ℤ-Mod (succ-ℕ k) = commutative-mul-Fin

left-unit-law-mul-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → Id (mul-ℤ-Mod k (one-ℤ-Mod k) x) x
left-unit-law-mul-ℤ-Mod zero-ℕ = left-unit-law-mul-ℤ
left-unit-law-mul-ℤ-Mod (succ-ℕ k) = left-unit-law-mul-Fin

right-unit-law-mul-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → Id (mul-ℤ-Mod k x (one-ℤ-Mod k)) x
right-unit-law-mul-ℤ-Mod zero-ℕ = right-unit-law-mul-ℤ
right-unit-law-mul-ℤ-Mod (succ-ℕ k) = right-unit-law-mul-Fin

left-distributive-mul-add-ℤ-Mod :
  (k : ℕ) (x y z : ℤ-Mod k) →
  Id ( mul-ℤ-Mod k x (add-ℤ-Mod k y z))
     ( add-ℤ-Mod k (mul-ℤ-Mod k x y) (mul-ℤ-Mod k x z))
left-distributive-mul-add-ℤ-Mod zero-ℕ = left-distributive-mul-add-ℤ
left-distributive-mul-add-ℤ-Mod (succ-ℕ k) = left-distributive-mul-add-Fin

right-distributive-mul-add-ℤ-Mod :
  (k : ℕ) (x y z : ℤ-Mod k) →
  Id ( mul-ℤ-Mod k (add-ℤ-Mod k x y) z)
     ( add-ℤ-Mod k (mul-ℤ-Mod k x z) (mul-ℤ-Mod k y z))
right-distributive-mul-add-ℤ-Mod zero-ℕ = right-distributive-mul-add-ℤ
right-distributive-mul-add-ℤ-Mod (succ-ℕ k) = right-distributive-mul-add-Fin

is-mul-neg-one-neg-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → Id (neg-ℤ-Mod k x) (mul-ℤ-Mod k (neg-one-ℤ-Mod k) x)
is-mul-neg-one-neg-ℤ-Mod zero-ℕ = is-mul-neg-one-neg-ℤ
is-mul-neg-one-neg-ℤ-Mod (succ-ℕ k) = is-mul-neg-one-neg-Fin

is-mul-neg-one-neg-ℤ-Mod' :
  (k : ℕ) (x : ℤ-Mod k) → Id (neg-ℤ-Mod k x) (mul-ℤ-Mod k x (neg-one-ℤ-Mod k))
is-mul-neg-one-neg-ℤ-Mod' zero-ℕ = is-mul-neg-one-neg-ℤ'
is-mul-neg-one-neg-ℤ-Mod' (succ-ℕ k) = is-mul-neg-one-neg-Fin'
```

## Congruence classes of integers modulo k

```agda
mod-ℕ : (k : ℕ) → ℕ → ℤ-Mod k
mod-ℕ zero-ℕ x = int-ℕ x
mod-ℕ (succ-ℕ k) x = mod-succ-ℕ k x

mod-ℤ : (k : ℕ) → ℤ → ℤ-Mod k
mod-ℤ zero-ℕ x = x
mod-ℤ (succ-ℕ k) (inl x) = neg-Fin (mod-succ-ℕ k (succ-ℕ x))
mod-ℤ (succ-ℕ k) (inr (inl x)) = zero-Fin
mod-ℤ (succ-ℕ k) (inr (inr x)) = mod-succ-ℕ k (succ-ℕ x)
```

## Preservation laws of congruence classes

```agda
mod-zero-ℕ : (k : ℕ) → Id (mod-ℕ k zero-ℕ) (zero-ℤ-Mod k)
mod-zero-ℕ zero-ℕ = refl
mod-zero-ℕ (succ-ℕ k) = refl

preserves-successor-mod-ℕ :
  (k x : ℕ) → Id (mod-ℕ k (succ-ℕ x)) (succ-ℤ-Mod k (mod-ℕ k x))
preserves-successor-mod-ℕ zero-ℕ zero-ℕ = refl
preserves-successor-mod-ℕ zero-ℕ (succ-ℕ x) = refl
preserves-successor-mod-ℕ (succ-ℕ k) x = refl

mod-zero-ℤ : (k : ℕ) → Id (mod-ℤ k zero-ℤ) (zero-ℤ-Mod k)
mod-zero-ℤ zero-ℕ = refl
mod-zero-ℤ (succ-ℕ k) = refl

mod-one-ℤ : (k : ℕ) → Id (mod-ℤ k one-ℤ) (one-ℤ-Mod k)
mod-one-ℤ zero-ℕ = refl
mod-one-ℤ (succ-ℕ k) = refl

mod-neg-one-ℤ : (k : ℕ) → Id (mod-ℤ k neg-one-ℤ) (neg-one-ℤ-Mod k)
mod-neg-one-ℤ zero-ℕ = refl
mod-neg-one-ℤ (succ-ℕ k) =
  ( neg-succ-Fin zero-Fin) ∙
  ( ( ap pred-Fin neg-zero-Fin) ∙
    ( ( is-add-neg-one-pred-Fin' zero-Fin) ∙
      ( left-unit-law-add-Fin neg-one-Fin)))

preserves-successor-mod-ℤ :
  (k : ℕ) (x : ℤ) → Id (mod-ℤ k (succ-ℤ x)) (succ-ℤ-Mod k (mod-ℤ k x))
preserves-successor-mod-ℤ zero-ℕ x = refl
preserves-successor-mod-ℤ (succ-ℕ k) (inl zero-ℕ) =
  inv (ap succ-Fin is-neg-one-neg-one-Fin)
preserves-successor-mod-ℤ (succ-ℕ k) (inl (succ-ℕ x)) =
  ( ap neg-Fin (inv (isretr-pred-Fin (succ-Fin (mod-succ-ℕ k x))))) ∙
  ( neg-pred-Fin (succ-Fin (succ-Fin (mod-succ-ℕ k x))))
preserves-successor-mod-ℤ (succ-ℕ k) (inr (inl star)) = refl
preserves-successor-mod-ℤ (succ-ℕ k) (inr (inr x)) = refl

preserves-predecessor-mod-ℤ :
  (k : ℕ) (x : ℤ) → Id (mod-ℤ k (pred-ℤ x)) (pred-ℤ-Mod k (mod-ℤ k x))
preserves-predecessor-mod-ℤ zero-ℕ x = refl
preserves-predecessor-mod-ℤ (succ-ℕ k) (inl x) =
  neg-succ-Fin (succ-Fin (mod-succ-ℕ k x))
preserves-predecessor-mod-ℤ (succ-ℕ k) (inr (inl star)) =
  ( is-neg-one-neg-one-Fin) ∙
  ( ( inv (left-unit-law-add-Fin neg-one-Fin)) ∙
    ( inv (is-add-neg-one-pred-Fin' zero-Fin)))
preserves-predecessor-mod-ℤ (succ-ℕ k) (inr (inr zero-ℕ)) =
  inv
    ( ( ap pred-Fin (preserves-successor-mod-ℤ (succ-ℕ k) zero-ℤ)) ∙
      ( isretr-pred-Fin zero-Fin))
preserves-predecessor-mod-ℤ (succ-ℕ k) (inr (inr (succ-ℕ x))) =
  inv (isretr-pred-Fin (succ-Fin (mod-succ-ℕ k x)))

preserves-add-mod-ℤ :
  (k : ℕ) (x y : ℤ) →
  Id (mod-ℤ k (add-ℤ x y)) (add-ℤ-Mod k (mod-ℤ k x) (mod-ℤ k y))
preserves-add-mod-ℤ zero-ℕ x y = refl
preserves-add-mod-ℤ (succ-ℕ k) (inl zero-ℕ) y =
  ( preserves-predecessor-mod-ℤ (succ-ℕ k) y) ∙
  ( ( is-add-neg-one-pred-Fin (mod-ℤ (succ-ℕ k) y)) ∙
    ( ap (add-Fin' (mod-ℤ (succ-ℕ k) y)) (inv (mod-neg-one-ℤ (succ-ℕ k)))))
preserves-add-mod-ℤ (succ-ℕ k) (inl (succ-ℕ x)) y =
  ( preserves-predecessor-mod-ℤ (succ-ℕ k) (add-ℤ (inl x) y)) ∙
  ( ( ap pred-Fin (preserves-add-mod-ℤ (succ-ℕ k) (inl x) y)) ∙
    ( ( inv
        ( left-predecessor-law-add-Fin
          ( mod-ℤ (succ-ℕ k) (inl x))
          ( mod-ℤ (succ-ℕ k) y))) ∙
      ( ap
        ( add-Fin' (mod-ℤ (succ-ℕ k) y))
        ( inv (preserves-predecessor-mod-ℤ (succ-ℕ k) (inl x))))))
preserves-add-mod-ℤ (succ-ℕ k) (inr (inl star)) y =
  inv (left-unit-law-add-Fin (mod-ℤ (succ-ℕ k) y))
preserves-add-mod-ℤ (succ-ℕ k) (inr (inr zero-ℕ)) y =
  ( preserves-successor-mod-ℤ (succ-ℕ k) y) ∙
  ( ( ap succ-Fin (inv (left-unit-law-add-Fin (mod-ℤ (succ-ℕ k) y)))) ∙
    ( inv (left-successor-law-add-Fin zero-Fin (mod-ℤ (succ-ℕ k) y))))
preserves-add-mod-ℤ (succ-ℕ k) (inr (inr (succ-ℕ x))) y =
  ( preserves-successor-mod-ℤ (succ-ℕ k) (add-ℤ (inr (inr x)) y)) ∙
  ( ( ap succ-Fin (preserves-add-mod-ℤ (succ-ℕ k) (inr (inr x)) y)) ∙
    ( inv
      ( left-successor-law-add-Fin
        ( mod-ℤ (succ-ℕ k) (inr (inr x)))
        ( mod-ℤ (succ-ℕ k) y))))

preserves-neg-mod-ℤ :
  (k : ℕ) (x : ℤ) → Id (mod-ℤ k (neg-ℤ x)) (neg-ℤ-Mod k (mod-ℤ k x))
preserves-neg-mod-ℤ zero-ℕ x = refl
preserves-neg-mod-ℤ (succ-ℕ k) x =
  is-injective-add-Fin
    ( mod-ℤ (succ-ℕ k) x)
    ( ( inv (preserves-add-mod-ℤ (succ-ℕ k) x (neg-ℤ x))) ∙
      ( ( ap (mod-ℤ (succ-ℕ k)) (right-inverse-law-add-ℤ x)) ∙
        ( inv (right-inverse-law-add-ℤ-Mod (succ-ℕ k) (mod-ℤ (succ-ℕ k) x)))))

preserves-mul-mod-ℤ :
  (k : ℕ) (x y : ℤ) →
  Id (mod-ℤ k (mul-ℤ x y)) (mul-ℤ-Mod k (mod-ℤ k x) (mod-ℤ k y))
preserves-mul-mod-ℤ zero-ℕ x y = refl
preserves-mul-mod-ℤ (succ-ℕ k) (inl zero-ℕ) y =
  ( preserves-neg-mod-ℤ (succ-ℕ k) y) ∙
  ( ( is-mul-neg-one-neg-Fin (mod-ℤ (succ-ℕ k) y)) ∙
    ( ap
      ( mul-ℤ-Mod' (succ-ℕ k) (mod-ℤ (succ-ℕ k) y))
      ( inv (mod-neg-one-ℤ (succ-ℕ k)))))
preserves-mul-mod-ℤ (succ-ℕ k) (inl (succ-ℕ x)) y =
  ( preserves-add-mod-ℤ (succ-ℕ k) (neg-ℤ y) (mul-ℤ (inl x) y)) ∙
  ( ( ap-add-ℤ-Mod
      ( succ-ℕ k)
      ( preserves-neg-mod-ℤ (succ-ℕ k) y)
      ( preserves-mul-mod-ℤ (succ-ℕ k) (inl x) y)) ∙
    ( ( inv
        ( left-predecessor-law-mul-Fin
          ( mod-ℤ (succ-ℕ k) (inl x))
          ( mod-ℤ (succ-ℕ k) y))) ∙
      ( ap
        ( mul-Fin' (mod-ℤ (succ-ℕ k) y))
        ( inv (preserves-predecessor-mod-ℤ (succ-ℕ k) (inl x))))))
preserves-mul-mod-ℤ (succ-ℕ k) (inr (inl star)) y =
  inv (left-zero-law-mul-Fin (mod-ℤ (succ-ℕ k) y))
preserves-mul-mod-ℤ (succ-ℕ k) (inr (inr zero-ℕ)) y =
  inv (left-unit-law-mul-Fin (mod-ℤ (succ-ℕ k) y))
preserves-mul-mod-ℤ (succ-ℕ k) (inr (inr (succ-ℕ x))) y =
  ( preserves-add-mod-ℤ (succ-ℕ k) y (mul-ℤ (inr (inr x)) y)) ∙
  ( ( ap
      ( add-ℤ-Mod (succ-ℕ k) (mod-ℤ (succ-ℕ k) y))
      ( preserves-mul-mod-ℤ (succ-ℕ k) (inr (inr x)) y)) ∙
    ( inv
      ( left-successor-law-mul-Fin
        ( mod-ℤ (succ-ℕ k) (inr (inr x)))
        ( mod-ℤ (succ-ℕ k) y))))
```

```agda
cong-int-mod-ℕ :
  (k x : ℕ) → cong-ℤ (int-ℕ k) (int-ℤ-Mod k (mod-ℕ k x)) (int-ℕ x)
cong-int-mod-ℕ zero-ℕ x = refl-cong-ℤ zero-ℤ (int-ℕ x)
cong-int-mod-ℕ (succ-ℕ k) x =
  cong-int-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (mod-succ-ℕ k x))
    ( x)
    ( cong-nat-mod-succ-ℕ k x)

cong-int-mod-ℤ :
  (k : ℕ) (x : ℤ) → cong-ℤ (int-ℕ k) (int-ℤ-Mod k (mod-ℤ k x)) x
cong-int-mod-ℤ zero-ℕ x = refl-cong-ℤ zero-ℤ x
cong-int-mod-ℤ (succ-ℕ k) (inl x) =
  concatenate-eq-cong-ℤ
    ( int-ℕ (succ-ℕ k))
    ( int-ℤ-Mod (succ-ℕ k) (mod-ℤ (succ-ℕ k) (inl x)))
    ( int-ℕ (nat-Fin (mul-Fin neg-one-Fin (mod-succ-ℕ k (succ-ℕ x)))))
    ( inl x)
    ( ap
      ( int-ℤ-Mod (succ-ℕ k))
      ( preserves-mul-mod-ℤ (succ-ℕ k) neg-one-ℤ (inr (inr x)) ∙
        ap (mul-Fin' (mod-succ-ℕ k (succ-ℕ x))) (mod-neg-one-ℤ (succ-ℕ k))))
    ( transitive-cong-ℤ
      ( int-ℕ (succ-ℕ k))
      ( int-ℕ (nat-Fin (mul-Fin neg-one-Fin (mod-succ-ℕ k (succ-ℕ x)))))
      ( int-ℕ (mul-ℕ k (nat-Fin (mod-succ-ℕ k (succ-ℕ x)))))
      ( inl x)
      ( cong-int-cong-ℕ
        ( succ-ℕ k)
        ( nat-Fin (mul-Fin neg-one-Fin (mod-succ-ℕ k (succ-ℕ x))))
        ( mul-ℕ k (nat-Fin (mod-succ-ℕ k (succ-ℕ x))))
        ( cong-mul-Fin neg-one-Fin (mod-succ-ℕ k (succ-ℕ x))))
      ( transitive-cong-ℤ
        ( int-ℕ (succ-ℕ k))
        ( int-ℕ (mul-ℕ k (nat-Fin (mod-succ-ℕ k (succ-ℕ x)))))
        ( int-ℕ (mul-ℕ k (succ-ℕ x)))
        ( inl x)
        ( cong-int-cong-ℕ
          ( succ-ℕ k)
          ( mul-ℕ k (nat-Fin (mod-succ-ℕ k (succ-ℕ x))))
          ( mul-ℕ k (succ-ℕ x))
          ( congruence-mul-ℕ
            ( succ-ℕ k)
            {k} {nat-Fin (mod-succ-ℕ k (succ-ℕ x))} {k} {succ-ℕ x}
            ( refl-cong-ℕ (succ-ℕ k) k)
            ( cong-nat-mod-succ-ℕ k (succ-ℕ x))))
        ( pair
          ( inr (inr x))
          ( ( commutative-mul-ℤ (inr (inr x)) (inr (inr k))) ∙
            ( ( ap
                ( mul-ℤ' (inr (inr x)))
                ( inv (succ-int-ℕ k) ∙ commutative-add-ℤ one-ℤ (int-ℕ k))) ∙
              ( ( right-distributive-mul-add-ℤ (int-ℕ k) one-ℤ (inr (inr x))) ∙
                ( ap-add-ℤ
                  ( mul-int-ℕ k (succ-ℕ x))
                  ( left-unit-law-mul-ℤ (inr (inr x))))))))))
cong-int-mod-ℤ (succ-ℕ k) (inr (inl star)) =
  cong-int-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (mod-succ-ℕ k zero-ℕ))
    ( zero-ℕ)
    ( cong-nat-mod-succ-ℕ k zero-ℕ)
cong-int-mod-ℤ (succ-ℕ k) (inr (inr x)) = 
  cong-int-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ x)
    ( cong-nat-mod-succ-ℕ k (succ-ℕ x))

cong-eq-mod-ℤ :
  (k : ℕ) (x y : ℤ) → Id (mod-ℤ k x) (mod-ℤ k y) → cong-ℤ (int-ℕ k) x y
cong-eq-mod-ℤ k x y p =
  concatenate-cong-eq-cong-ℤ
    ( int-ℕ k)
    ( x)
    ( int-ℤ-Mod k (mod-ℤ k x))
    ( int-ℤ-Mod k (mod-ℤ k y))
    ( y)
    ( symmetric-cong-ℤ
      (int-ℕ k)
      (int-ℤ-Mod k (mod-ℤ k x))
      ( x)
      ( cong-int-mod-ℤ k x))
    ( ap (int-ℤ-Mod k) p)
    ( cong-int-mod-ℤ k y)

eq-cong-int-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) →
  cong-ℤ (int-ℕ k) (int-ℤ-Mod k x) (int-ℤ-Mod k y) → Id x y
eq-cong-int-ℤ-Mod zero-ℕ = is-discrete-cong-ℤ zero-ℤ refl
eq-cong-int-ℤ-Mod (succ-ℕ k) x y H =
  eq-cong-nat-Fin (succ-ℕ k) x y
    ( cong-cong-int-ℕ (succ-ℕ k) (nat-Fin x) (nat-Fin y) H)

eq-mod-cong-ℤ :
  (k : ℕ) (x y : ℤ) → cong-ℤ (int-ℕ k) x y → Id (mod-ℤ k x) (mod-ℤ k y)
eq-mod-cong-ℤ k x y H =
  eq-cong-int-ℤ-Mod k
    ( mod-ℤ k x)
    ( mod-ℤ k y)
    ( concatenate-cong-cong-cong-ℤ
      ( int-ℕ k)
      ( int-ℤ-Mod k (mod-ℤ k x))
      ( x)
      ( y)
      ( int-ℤ-Mod k (mod-ℤ k y))
      ( cong-int-mod-ℤ k x)
      ( H)
      ( symmetric-cong-ℤ
        ( int-ℕ k)
        ( int-ℤ-Mod k (mod-ℤ k y))
        ( y)
        ( cong-int-mod-ℤ k y)))

is-zero-mod-div-ℤ :
  (k : ℕ) (x : ℤ) → div-ℤ (int-ℕ k) x → is-zero-ℤ-Mod k (mod-ℤ k x)
is-zero-mod-div-ℤ zero-ℕ x d = is-zero-div-zero-ℤ x d
is-zero-mod-div-ℤ (succ-ℕ k) x H =
  eq-mod-cong-ℤ
    ( succ-ℕ k)
    ( x)
    ( zero-ℤ)
    ( is-cong-zero-div-ℤ (int-ℕ (succ-ℕ k)) x H)

div-is-zero-mod-ℤ :
  (k : ℕ) (x : ℤ) → is-zero-ℤ-Mod k (mod-ℤ k x) → div-ℤ (int-ℕ k) x
div-is-zero-mod-ℤ zero-ℕ .zero-ℤ refl = refl-div-ℤ zero-ℤ
div-is-zero-mod-ℤ (succ-ℕ k) x p =
  div-is-cong-zero-ℤ
    ( int-ℕ (succ-ℕ k))
    ( x)
    ( cong-eq-mod-ℤ (succ-ℕ k) x zero-ℤ p)

issec-int-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → Id (mod-ℤ k (int-ℤ-Mod k x)) x
issec-int-ℤ-Mod k x =
  eq-cong-int-ℤ-Mod k
    ( mod-ℤ k (int-ℤ-Mod k x))
    ( x)
    ( cong-int-mod-ℤ k (int-ℤ-Mod k x))

is-one-is-fixed-point-succ-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → Id (succ-ℤ-Mod k x) x → is-one-ℕ k
is-one-is-fixed-point-succ-ℤ-Mod k x p =
  is-one-is-unit-int-ℕ k
    ( is-unit-cong-succ-ℤ
      ( int-ℕ k)
      ( int-ℤ-Mod k x)
      ( cong-eq-mod-ℤ k
        ( int-ℤ-Mod k x)
        ( succ-ℤ (int-ℤ-Mod k x))
        ( ( issec-int-ℤ-Mod k x) ∙
          ( ( inv p) ∙
            ( inv
              ( ( preserves-successor-mod-ℤ k (int-ℤ-Mod k x)) ∙
                ( ap (succ-ℤ-Mod k) (issec-int-ℤ-Mod k x))))))))

has-no-fixed-points-succ-ℤ-Mod :
  (k : ℕ) (x : ℤ-Mod k) → is-not-one-ℕ k → ¬ (Id (succ-ℤ-Mod k x) x)
has-no-fixed-points-succ-ℤ-Mod k x =
  functor-neg (is-one-is-fixed-point-succ-ℤ-Mod k x)

has-no-fixed-points-succ-Fin :
  {k : ℕ} (x : Fin k) → is-not-one-ℕ k → ¬ (Id (succ-Fin x) x)
has-no-fixed-points-succ-Fin {succ-ℕ k} x =
  has-no-fixed-points-succ-ℤ-Mod (succ-ℕ k) x
```
