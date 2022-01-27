---
title: Univalent Mathematics in Agda
---

# Modular arithmetic on the standard finite types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.modular-arithmetic-standard-finite-types where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; add-ℕ'; commutative-add-ℕ; associative-add-ℕ)
open import elementary-number-theory.congruence-natural-numbers using
  ( cong-ℕ; cong-identification-ℕ; concatenate-eq-cong-ℕ; cong-zero-ℕ';
    trans-cong-ℕ; concatenate-cong-eq-cong-ℕ; symm-cong-ℕ; eq-cong-nat-Fin;
    cong-is-zero-nat-zero-Fin; eq-cong-le-ℕ; concatenate-eq-cong-eq-ℕ;
    refl-cong-ℕ; congruence-mul-ℕ; translation-invariant-cong-ℕ;
    translation-invariant-cong-ℕ')
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-iff; is-decidable-neg)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import elementary-number-theory.distance-natural-numbers using
  ( dist-ℕ; right-unit-law-dist-ℕ; translation-invariant-dist-ℕ;
    is-difference-dist-ℕ'; is-one-dist-succ-ℕ)
open import elementary-number-theory.divisibility-natural-numbers using
  ( div-ℕ; concatenate-div-eq-ℕ; div-eq-ℕ; is-zero-div-zero-ℕ; is-even-ℕ;
    is-odd-ℕ)
open import elementary-number-theory.equality-natural-numbers using
  ( is-decidable-is-zero-ℕ')
open import elementary-number-theory.equality-standard-finite-types using
  ( is-decidable-is-zero-Fin)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap; ap-binary)
open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; concatenate-eq-leq-ℕ; refl-leq-ℕ; transitive-leq-ℕ)
open import foundation.injective-maps using (is-injective)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ; mul-ℕ'; associative-mul-ℕ; commutative-mul-ℕ; left-unit-law-mul-ℕ;
    left-distributive-mul-add-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import foundation.split-surjective-maps using (is-split-surjective)
open import elementary-number-theory.standard-finite-types using
  ( Fin; zero-Fin; succ-Fin; nat-Fin; nat-succ-Fin; is-zero-nat-zero-Fin;
    is-zero-Fin; is-injective-nat-Fin; strict-upper-bound-nat-Fin;
    upper-bound-nat-Fin; one-Fin; is-one-nat-one-Fin; neg-one-Fin; is-one-Fin;
    pred-Fin; is-injective-succ-Fin; issec-pred-Fin; leq-nat-succ-Fin)
open import foundation.unit-type using (star)
```

# Modular arithmetic

## The congruence class of a natural number modulo a successor

```agda
mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ k zero-ℕ = zero-Fin
mod-succ-ℕ k (succ-ℕ n) = succ-Fin (mod-succ-ℕ k n)

mod-two-ℕ : ℕ → Fin 2
mod-two-ℕ = mod-succ-ℕ 1

mod-three-ℕ : ℕ → Fin 3
mod-three-ℕ = mod-succ-ℕ 2
```

```agda
cong-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → cong-ℕ k (nat-Fin (succ-Fin x)) (succ-ℕ (nat-Fin x))
cong-nat-succ-Fin (succ-ℕ k) (inl x) =
  cong-identification-ℕ
    ( succ-ℕ k)
    { nat-Fin (succ-Fin (inl x))}
    { succ-ℕ (nat-Fin x)}
    ( nat-succ-Fin x)
cong-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-cong-ℕ
    ( succ-ℕ k)
    { nat-Fin {succ-ℕ k} zero-Fin}
    { zero-ℕ}
    { succ-ℕ k}
    ( is-zero-nat-zero-Fin {k})
    ( cong-zero-ℕ' (succ-ℕ k))

cong-nat-mod-succ-ℕ :
  (k x : ℕ) → cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
cong-nat-mod-succ-ℕ k zero-ℕ = cong-is-zero-nat-zero-Fin
cong-nat-mod-succ-ℕ k (succ-ℕ x) =
  trans-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( cong-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x) )
    ( cong-nat-mod-succ-ℕ k x)
```

We show that if mod-succ-ℕ k x = mod-succ-ℕ k y, then x and y must be congruent modulo succ-ℕ n. This is the forward direction of the theorem.

```agda
cong-eq-mod-succ-ℕ :
  (k x y : ℕ) → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y) → cong-ℕ (succ-ℕ k) x y
cong-eq-mod-succ-ℕ k x y p =
  concatenate-cong-eq-cong-ℕ {succ-ℕ k} {x}
    ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
      ( cong-nat-mod-succ-ℕ k x))
    ( ap nat-Fin p)
    ( cong-nat-mod-succ-ℕ k y)
```

```agda
eq-mod-succ-cong-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y)
eq-mod-succ-cong-ℕ k x y H =
  eq-cong-nat-Fin
    ( succ-ℕ k)
    ( mod-succ-ℕ k x)
    ( mod-succ-ℕ k y)
    ( trans-cong-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k x))
      ( x)
      ( nat-Fin (mod-succ-ℕ k y))
      ( cong-nat-mod-succ-ℕ k x)
      ( trans-cong-ℕ (succ-ℕ k) x y (nat-Fin (mod-succ-ℕ k y)) H
        ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k y)) y
          ( cong-nat-mod-succ-ℕ k y))))
```          

```agda
is-zero-mod-succ-ℕ :
  (k x : ℕ) → div-ℕ (succ-ℕ k) x → is-zero-Fin (mod-succ-ℕ k x)
is-zero-mod-succ-ℕ k x d =
  eq-mod-succ-cong-ℕ k x zero-ℕ
    ( concatenate-div-eq-ℕ d (inv (right-unit-law-dist-ℕ x)))

div-is-zero-mod-succ-ℕ :
  (k x : ℕ) → is-zero-Fin (mod-succ-ℕ k x) → div-ℕ (succ-ℕ k) x
div-is-zero-mod-succ-ℕ k x p =
  concatenate-div-eq-ℕ
    ( cong-eq-mod-succ-ℕ k x zero-ℕ p)
    ( right-unit-law-dist-ℕ x)
```

### The inclusion of Fin k into ℕ is a section of mod-succ-ℕ

```agda
issec-nat-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mod-succ-ℕ k (nat-Fin x)) x
issec-nat-Fin {k} x =
  is-injective-nat-Fin
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k (nat-Fin x)))
      ( nat-Fin x)
      ( strict-upper-bound-nat-Fin (mod-succ-ℕ k (nat-Fin x)))
      ( strict-upper-bound-nat-Fin x)
      ( cong-nat-mod-succ-ℕ k (nat-Fin x)))

is-split-surjective-mod-succ-ℕ :
  {k : ℕ} → is-split-surjective (mod-succ-ℕ k)
pr1 (is-split-surjective-mod-succ-ℕ {k} x) = nat-Fin x
pr2 (is-split-surjective-mod-succ-ℕ {k} x) = issec-nat-Fin x
```

## The group structure on the standard finite types

### Addition on finite sets

```agda
add-Fin : {k : ℕ} → Fin k → Fin k → Fin k
add-Fin {succ-ℕ k} x y = mod-succ-ℕ k (add-ℕ (nat-Fin x) (nat-Fin y))

add-Fin' : {k : ℕ} → Fin k → Fin k → Fin k
add-Fin' x y = add-Fin y x

ap-add-Fin :
  {k : ℕ} {x y x' y' : Fin k} →
  Id x x' → Id y y' → Id (add-Fin x y) (add-Fin x' y')
ap-add-Fin p q = ap-binary add-Fin p q

cong-add-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (add-Fin x y)) (add-ℕ (nat-Fin x) (nat-Fin y))
cong-add-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (add-ℕ (nat-Fin x) (nat-Fin y))
```

### The negative of an element of Fin k

```agda
neg-Fin :
  {k : ℕ} → Fin k → Fin k
neg-Fin {succ-ℕ k} x =
  mod-succ-ℕ k (dist-ℕ (nat-Fin x) (succ-ℕ k))

cong-neg-Fin :
  {k : ℕ} (x : Fin k) →
  cong-ℕ k (nat-Fin (neg-Fin x)) (dist-ℕ (nat-Fin x) k)
cong-neg-Fin {succ-ℕ k} x =
  cong-nat-mod-succ-ℕ k (dist-ℕ (nat-Fin x) (succ-ℕ k))
```

```agda
congruence-add-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k y y' → cong-ℕ k (add-ℕ x y) (add-ℕ x' y')
congruence-add-ℕ k {x} {y} {x'} {y'} H K =
  trans-cong-ℕ k (add-ℕ x y) (add-ℕ x y') (add-ℕ x' y')
    ( translation-invariant-cong-ℕ k y y' x K)
    ( translation-invariant-cong-ℕ' k x x' y' H)

mod-succ-add-ℕ :
  (k x y : ℕ) →
  Id (mod-succ-ℕ k (add-ℕ x y)) (add-Fin (mod-succ-ℕ k x) (mod-succ-ℕ k y))
mod-succ-add-ℕ k x y =
  eq-mod-succ-cong-ℕ k
    ( add-ℕ x y)
    ( add-ℕ (nat-Fin (mod-succ-ℕ k x)) (nat-Fin (mod-succ-ℕ k y)))
    ( congruence-add-ℕ
      ( succ-ℕ k)
      { x}
      { y}
      { nat-Fin (mod-succ-ℕ k x)}
      { nat-Fin (mod-succ-ℕ k y)}
      ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
        ( cong-nat-mod-succ-ℕ k x))
      ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k y)) y
        ( cong-nat-mod-succ-ℕ k y)))
```

## Laws for addition on Fin k

```agda
commutative-add-Fin : {k : ℕ} (x y : Fin k) → Id (add-Fin x y) (add-Fin y x)
commutative-add-Fin {succ-ℕ k} x y =
  ap (mod-succ-ℕ k) (commutative-add-ℕ (nat-Fin x) (nat-Fin y))

associative-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (add-Fin (add-Fin x y) z) (add-Fin x (add-Fin y z))
associative-add-Fin {succ-ℕ k} x y z =
  eq-mod-succ-cong-ℕ k
    ( add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z))
    ( add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z)}
      { x2 = add-ℕ (add-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = add-ℕ (nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z))}
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (add-Fin x y)}
        { y = nat-Fin z}
        { x' = add-ℕ (nat-Fin x) (nat-Fin y)}
        { y' = nat-Fin z}
        ( cong-add-Fin x y)
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin x}
        { y = add-ℕ (nat-Fin y) (nat-Fin z)}
        { x' = nat-Fin x}
        { y' = nat-Fin (add-Fin y z)}
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin x))
        ( symm-cong-ℕ
          ( succ-ℕ k)
          ( nat-Fin (add-Fin y z))
          ( add-ℕ (nat-Fin y) (nat-Fin z))
          ( cong-add-Fin y z))))

right-unit-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin x zero-Fin) x
right-unit-law-add-Fin {k} x =
  ( eq-mod-succ-cong-ℕ k
    ( add-ℕ (nat-Fin x) (nat-Fin {succ-ℕ k} zero-Fin))
    ( add-ℕ (nat-Fin x) zero-ℕ)
    ( congruence-add-ℕ
      ( succ-ℕ k)
      { x = nat-Fin {succ-ℕ k} x}
      { y = nat-Fin {succ-ℕ k} zero-Fin}
      { x' = nat-Fin x}
      { y' = zero-ℕ}
      ( refl-cong-ℕ (succ-ℕ k) (nat-Fin {succ-ℕ k} x))
      ( cong-is-zero-nat-zero-Fin {k}))) ∙
  ( issec-nat-Fin x)

left-unit-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin zero-Fin x) x
left-unit-law-add-Fin {k} x =
  ( commutative-add-Fin zero-Fin x) ∙
  ( right-unit-law-add-Fin x)

left-inverse-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-zero-Fin (add-Fin (neg-Fin x) x)
left-inverse-law-add-Fin {k} x =
  eq-mod-succ-cong-ℕ k
    ( add-ℕ (nat-Fin (neg-Fin x)) (nat-Fin x))
    ( zero-ℕ)
    ( concatenate-cong-eq-cong-ℕ
      { succ-ℕ k}
      { x1 = add-ℕ (nat-Fin (neg-Fin x)) (nat-Fin x)}
      { x2 = add-ℕ (dist-ℕ (nat-Fin x) (succ-ℕ k)) (nat-Fin x)}
      { x3 = succ-ℕ k}
      { x4 = zero-ℕ}
      ( translation-invariant-cong-ℕ' (succ-ℕ k)
        ( nat-Fin (neg-Fin x))
        ( dist-ℕ (nat-Fin x) (succ-ℕ k))
        ( nat-Fin x)
        ( cong-neg-Fin x))
      ( is-difference-dist-ℕ' (nat-Fin x) (succ-ℕ k)
        ( upper-bound-nat-Fin (inl x)))
      ( cong-zero-ℕ' (succ-ℕ k)))

right-inverse-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-zero-Fin (add-Fin x (neg-Fin x))
right-inverse-law-add-Fin x =
  ( commutative-add-Fin x (neg-Fin x)) ∙ (left-inverse-law-add-Fin x)
```

```agda
is-add-one-succ-Fin' :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (succ-Fin x) (add-Fin x one-Fin)
is-add-one-succ-Fin' {zero-ℕ} (inr star) = refl
is-add-one-succ-Fin' {succ-ℕ k} x =
  ( ap succ-Fin (inv (issec-nat-Fin x))) ∙
  ( ap ( mod-succ-ℕ  (succ-ℕ k))
       ( ap (add-ℕ (nat-Fin x)) (inv (is-one-nat-one-Fin (succ-ℕ k)))))

is-add-one-succ-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (succ-Fin x) (add-Fin one-Fin x)
is-add-one-succ-Fin x = is-add-one-succ-Fin' x ∙ commutative-add-Fin x one-Fin

-- We conclude the successor laws for addition on Fin k

right-successor-law-add-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin x (succ-Fin y)) (succ-Fin (add-Fin x y))
right-successor-law-add-Fin {succ-ℕ k} x y =
  ( ap (add-Fin x) (is-add-one-succ-Fin' y)) ∙
  ( ( inv (associative-add-Fin x y one-Fin)) ∙
    ( inv (is-add-one-succ-Fin' (add-Fin x y))))

left-successor-law-add-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin (succ-Fin x) y) (succ-Fin (add-Fin x y))
left-successor-law-add-Fin x y =
  commutative-add-Fin (succ-Fin x) y ∙
  ( ( right-successor-law-add-Fin y x) ∙
    ( ap succ-Fin (commutative-add-Fin y x)))
```

## Multiplication on Fin k

```agda
{- We define the multiplication on the types Fin k. -}

mul-Fin :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin {succ-ℕ k} x y = mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

mul-Fin' :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin' {k} x y = mul-Fin y x

ap-mul-Fin :
  {k : ℕ} {x y x' y' : Fin k} →
  Id x x' → Id y y' → Id (mul-Fin x y) (mul-Fin x' y')
ap-mul-Fin p q = ap-binary mul-Fin p q

cong-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (mul-Fin x y)) (mul-ℕ (nat-Fin x) (nat-Fin y))
cong-mul-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))
```

## Laws for multiplication on the standard finite types

```agda
associative-mul-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (mul-Fin x y) z) (mul-Fin x (mul-Fin y z))
associative-mul-Fin {succ-ℕ k} x y z =
  eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z))
    ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z)}
      { x2 = mul-ℕ (mul-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (mul-Fin x y)}
        { y = nat-Fin z}
        ( cong-mul-Fin x y)
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-mul-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symm-cong-ℕ
        ( succ-ℕ k)
        ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
        ( mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z)))
        ( congruence-mul-ℕ
          ( succ-ℕ k)
          { x = nat-Fin x}
          { y = nat-Fin (mul-Fin y z)}
          ( refl-cong-ℕ (succ-ℕ k) (nat-Fin x))
          ( cong-mul-Fin y z))))

commutative-mul-Fin :
  {k : ℕ} (x y : Fin k) → Id (mul-Fin x y) (mul-Fin y x)
commutative-mul-Fin {succ-ℕ k} x y =
  eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin y))
    ( mul-ℕ (nat-Fin y) (nat-Fin x))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( commutative-mul-ℕ (nat-Fin x) (nat-Fin y)))

left-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin one-Fin x) x
left-unit-law-mul-Fin {zero-ℕ} (inr star) = refl
left-unit-law-mul-Fin {succ-ℕ k} x =
  ( eq-mod-succ-cong-ℕ (succ-ℕ k)
    ( mul-ℕ (nat-Fin (one-Fin {succ-ℕ k})) (nat-Fin x))
    ( nat-Fin x)
    ( cong-identification-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( ( ap ( mul-ℕ' (nat-Fin x))
             ( is-one-nat-one-Fin k)) ∙
        ( left-unit-law-mul-ℕ (nat-Fin x))))) ∙
  ( issec-nat-Fin x)

right-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x one-Fin) x
right-unit-law-mul-Fin x =
  ( commutative-mul-Fin x one-Fin) ∙
  ( left-unit-law-mul-Fin x)

left-zero-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin zero-Fin x) zero-Fin
left-zero-law-mul-Fin {k} x =
  ( eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin (zero-Fin {k})) (nat-Fin x))
    ( nat-Fin (zero-Fin {k}))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      { mul-ℕ (nat-Fin (zero-Fin {k})) (nat-Fin x)}
      { nat-Fin (zero-Fin {k})}
      ( ( ap (mul-ℕ' (nat-Fin x)) (is-zero-nat-zero-Fin {k})) ∙
        ( inv (is-zero-nat-zero-Fin {k}))))) ∙
  ( issec-nat-Fin (zero-Fin {k}))

right-zero-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x zero-Fin) zero-Fin
right-zero-law-mul-Fin x =
  ( commutative-mul-Fin x zero-Fin) ∙
  ( left-zero-law-mul-Fin x)

left-distributive-mul-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin x (add-Fin y z)) (add-Fin (mul-Fin x y) (mul-Fin x z))
left-distributive-mul-add-Fin {succ-ℕ k} x y z =
  eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( add-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin (mul-Fin x z)))
    ( concatenate-cong-eq-cong-ℕ
      { k = succ-ℕ k}
      { x1 = mul-ℕ ( nat-Fin x) (nat-Fin (add-Fin y z))}
      { x2 = mul-ℕ ( nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x3 = add-ℕ ( mul-ℕ (nat-Fin x) (nat-Fin y))
                   ( mul-ℕ (nat-Fin x) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin (mul-Fin x z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin x}
        { y = nat-Fin (add-Fin y z)}
        { x' = nat-Fin x}
        { y' = add-ℕ (nat-Fin y) (nat-Fin z)}
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin x))
        ( cong-add-Fin y z))
      ( left-distributive-mul-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symm-cong-ℕ (succ-ℕ k)
        ( add-ℕ ( nat-Fin (mul-Fin x y))
                ( nat-Fin (mul-Fin x z)))
        ( add-ℕ ( mul-ℕ (nat-Fin x) (nat-Fin y))
                ( mul-ℕ (nat-Fin x) (nat-Fin z)))
        ( congruence-add-ℕ
          ( succ-ℕ k)
          { x = nat-Fin (mul-Fin x y)}
          { y = nat-Fin (mul-Fin x z)}
          { x' = mul-ℕ (nat-Fin x) (nat-Fin y)}
          { y' = mul-ℕ (nat-Fin x) (nat-Fin z)}
          ( cong-mul-Fin x y)
          ( cong-mul-Fin x z))))

right-distributive-mul-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (add-Fin x y) z) (add-Fin (mul-Fin x z) (mul-Fin y z))
right-distributive-mul-add-Fin {k} x y z =
  ( commutative-mul-Fin (add-Fin x y) z) ∙
  ( ( left-distributive-mul-add-Fin z x y) ∙
    ( ap-add-Fin (commutative-mul-Fin z x) (commutative-mul-Fin z y)))
```

```agda
add-add-neg-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin x (add-Fin (neg-Fin x) y)) y
add-add-neg-Fin {succ-ℕ k} x y =
  ( inv (associative-add-Fin x (neg-Fin x) y)) ∙
  ( ( ap (add-Fin' y) (right-inverse-law-add-Fin x)) ∙
    ( left-unit-law-add-Fin y))

add-neg-add-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin (neg-Fin x) (add-Fin x y)) y
add-neg-add-Fin {succ-ℕ k} x y =
  ( inv (associative-add-Fin (neg-Fin x) x y)) ∙
  ( ( ap (add-Fin' y) (left-inverse-law-add-Fin x)) ∙
    ( left-unit-law-add-Fin y))

is-equiv-add-Fin :
  {k : ℕ} (x : Fin k) → is-equiv (add-Fin x)
pr1 (pr1 (is-equiv-add-Fin x)) = add-Fin (neg-Fin x)
pr2 (pr1 (is-equiv-add-Fin x)) = add-add-neg-Fin x
pr1 (pr2 (is-equiv-add-Fin x)) = add-Fin (neg-Fin x)
pr2 (pr2 (is-equiv-add-Fin x)) = add-neg-add-Fin x

equiv-add-Fin :
  {k : ℕ} (x : Fin k) → Fin k ≃ Fin k
pr1 (equiv-add-Fin x) = add-Fin x
pr2 (equiv-add-Fin x) = is-equiv-add-Fin x

add-add-neg-Fin' :
  {k : ℕ} (x y : Fin k) → Id (add-Fin' x (add-Fin' (neg-Fin x) y)) y
add-add-neg-Fin' {succ-ℕ k} x y =
  ( associative-add-Fin y (neg-Fin x) x) ∙
  ( ( ap (add-Fin y) (left-inverse-law-add-Fin x)) ∙
    ( right-unit-law-add-Fin y))

add-neg-add-Fin' :
  {k : ℕ} (x y : Fin k) → Id (add-Fin' (neg-Fin x) (add-Fin' x y)) y
add-neg-add-Fin' {succ-ℕ k} x y =
  ( associative-add-Fin y x (neg-Fin x)) ∙
  ( ( ap (add-Fin y) (right-inverse-law-add-Fin x)) ∙
    ( right-unit-law-add-Fin y))

is-equiv-add-Fin' :
  {k : ℕ} (x : Fin k) → is-equiv (add-Fin' x)
pr1 (pr1 (is-equiv-add-Fin' x)) = add-Fin' (neg-Fin x)
pr2 (pr1 (is-equiv-add-Fin' x)) = add-add-neg-Fin' x
pr1 (pr2 (is-equiv-add-Fin' x)) = add-Fin' (neg-Fin x)
pr2 (pr2 (is-equiv-add-Fin' x)) = add-neg-add-Fin' x

equiv-add-Fin' :
  {k : ℕ} (x : Fin k) → Fin k ≃ Fin k
pr1 (equiv-add-Fin' x) = add-Fin' x
pr2 (equiv-add-Fin' x) = is-equiv-add-Fin' x

is-injective-add-Fin :
  {k : ℕ} (x : Fin k) → is-injective (add-Fin x)
is-injective-add-Fin {k} x {y} {z} p =
  ( inv (add-neg-add-Fin x y)) ∙
  ( ( ap (add-Fin (neg-Fin x)) p) ∙
    ( add-neg-add-Fin x z))

is-injective-add-Fin' :
  {k : ℕ} (x : Fin k) → is-injective (add-Fin' x)
is-injective-add-Fin' {k} x {y} {z} p =
  is-injective-add-Fin x
    (commutative-add-Fin x y ∙ (p ∙ commutative-add-Fin z x))
```

```agda
mul-neg-one-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin neg-one-Fin x) (neg-Fin x)
mul-neg-one-Fin {k} x =
  is-injective-add-Fin x
    ( ( ( ap
          ( add-Fin' (mul-Fin neg-one-Fin x))
          ( inv (left-unit-law-mul-Fin x))) ∙
        ( ( inv (right-distributive-mul-add-Fin one-Fin neg-one-Fin x)) ∙
          ( ( ap (mul-Fin' x) (inv (is-add-one-succ-Fin neg-one-Fin))) ∙
            ( left-zero-law-mul-Fin x)))) ∙
      ( inv (right-inverse-law-add-Fin x)))
```

```agda
is-one-neg-neg-one-Fin :
  {k : ℕ} → is-one-Fin {succ-ℕ k} (neg-Fin neg-one-Fin)
is-one-neg-neg-one-Fin {k} =
  eq-mod-succ-cong-ℕ k
    ( dist-ℕ k (succ-ℕ k))
    ( 1)
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( is-one-dist-succ-ℕ k))

is-neg-one-neg-one-Fin :
  {k : ℕ} → Id (neg-Fin {succ-ℕ k} one-Fin) neg-one-Fin
is-neg-one-neg-one-Fin {k} =
  is-injective-add-Fin one-Fin
    ( ( right-inverse-law-add-Fin one-Fin) ∙
      ( ( inv (left-inverse-law-add-Fin neg-one-Fin)) ∙
        ( ap (add-Fin' neg-one-Fin) is-one-neg-neg-one-Fin)))

is-add-neg-one-pred-Fin' :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (pred-Fin x) (add-Fin x neg-one-Fin)
is-add-neg-one-pred-Fin' {k} x =
  is-injective-succ-Fin
    ( ( issec-pred-Fin x) ∙
      ( ( ( ( inv (right-unit-law-add-Fin x)) ∙
            ( ap
              ( add-Fin x)
              ( inv
                ( ( ap (add-Fin' one-Fin) (inv is-neg-one-neg-one-Fin)) ∙
                  ( left-inverse-law-add-Fin one-Fin))))) ∙
          ( inv (associative-add-Fin x neg-one-Fin one-Fin))) ∙
        ( inv (is-add-one-succ-Fin' (add-Fin x neg-one-Fin)))))

is-add-neg-one-pred-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (pred-Fin x) (add-Fin neg-one-Fin x)
is-add-neg-one-pred-Fin x =
  is-add-neg-one-pred-Fin' x ∙ commutative-add-Fin x neg-one-Fin

is-mul-neg-one-neg-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (neg-Fin x) (mul-Fin neg-one-Fin x)
is-mul-neg-one-neg-Fin x =
  is-injective-add-Fin x
    ( ( right-inverse-law-add-Fin x) ∙
      ( ( ( ( inv (left-zero-law-mul-Fin x)) ∙
            ( ap
              ( mul-Fin' x)
              ( inv
                ( ( ap (add-Fin one-Fin) (inv is-neg-one-neg-one-Fin)) ∙
                  ( right-inverse-law-add-Fin one-Fin))))) ∙
          ( right-distributive-mul-add-Fin one-Fin neg-one-Fin x)) ∙
        ( ap (add-Fin' (mul-Fin neg-one-Fin x)) (left-unit-law-mul-Fin x))))

is-mul-neg-one-neg-Fin' :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (neg-Fin x) (mul-Fin x neg-one-Fin)
is-mul-neg-one-neg-Fin' x =
  is-mul-neg-one-neg-Fin x ∙ commutative-mul-Fin neg-one-Fin x

neg-zero-Fin : {k : ℕ} → Id (neg-Fin (zero-Fin {k})) zero-Fin
neg-zero-Fin {k} =
  ( inv (left-unit-law-add-Fin (neg-Fin zero-Fin))) ∙
  ( right-inverse-law-add-Fin zero-Fin)

neg-succ-Fin :
  {k : ℕ} (x : Fin k) → Id (neg-Fin (succ-Fin x)) (pred-Fin (neg-Fin x))
neg-succ-Fin {succ-ℕ k} x =
  ( ap neg-Fin (is-add-one-succ-Fin' x)) ∙
  ( ( is-mul-neg-one-neg-Fin (add-Fin x one-Fin)) ∙
    ( ( left-distributive-mul-add-Fin neg-one-Fin x one-Fin) ∙
      ( ( ap-add-Fin
          ( inv (is-mul-neg-one-neg-Fin x))
          ( inv (is-mul-neg-one-neg-Fin one-Fin) ∙ is-neg-one-neg-one-Fin)) ∙
        ( inv (is-add-neg-one-pred-Fin' (neg-Fin x))))))

neg-pred-Fin :
  {k : ℕ} (x : Fin k) → Id (neg-Fin (pred-Fin x)) (succ-Fin (neg-Fin x))
neg-pred-Fin {succ-ℕ k} x =
  ( ap neg-Fin (is-add-neg-one-pred-Fin' x)) ∙
  ( ( is-mul-neg-one-neg-Fin (add-Fin x neg-one-Fin)) ∙
    ( ( left-distributive-mul-add-Fin neg-one-Fin x neg-one-Fin) ∙
      ( ( ap-add-Fin
          ( inv (is-mul-neg-one-neg-Fin x))
          ( ( inv (is-mul-neg-one-neg-Fin neg-one-Fin)) ∙
            ( is-one-neg-neg-one-Fin))) ∙
        ( inv (is-add-one-succ-Fin' (neg-Fin x))))))

distributive-neg-add-Fin :
  {k : ℕ} (x y : Fin k) →
  Id (neg-Fin (add-Fin x y)) (add-Fin (neg-Fin x) (neg-Fin y))
distributive-neg-add-Fin {succ-ℕ k} x y =
  ( is-mul-neg-one-neg-Fin (add-Fin x y)) ∙
  ( ( left-distributive-mul-add-Fin neg-one-Fin x y) ∙
    ( inv (ap-add-Fin (is-mul-neg-one-neg-Fin x) (is-mul-neg-one-neg-Fin y))))

left-predecessor-law-add-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin (pred-Fin x) y) (pred-Fin (add-Fin x y))
left-predecessor-law-add-Fin {succ-ℕ k} x y =
  ( ap (add-Fin' y) (is-add-neg-one-pred-Fin x)) ∙
  ( ( associative-add-Fin neg-one-Fin x y) ∙
    ( inv (is-add-neg-one-pred-Fin (add-Fin x y))))

right-predecessor-law-add-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin x (pred-Fin y)) (pred-Fin (add-Fin x y))
right-predecessor-law-add-Fin {succ-ℕ k} x y =
  ( ap (add-Fin x) (is-add-neg-one-pred-Fin' y)) ∙
  ( ( inv (associative-add-Fin x y neg-one-Fin)) ∙
    ( inv (is-add-neg-one-pred-Fin' (add-Fin x y))))

left-negative-law-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  Id (mul-Fin (neg-Fin x) y) (neg-Fin (mul-Fin x y))
left-negative-law-mul-Fin {succ-ℕ k} x y =
  ( ap (mul-Fin' y) (is-mul-neg-one-neg-Fin x)) ∙
  ( ( associative-mul-Fin neg-one-Fin x y) ∙
    ( inv (is-mul-neg-one-neg-Fin (mul-Fin x y))))

right-negative-law-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  Id (mul-Fin x (neg-Fin y)) (neg-Fin (mul-Fin x y))
right-negative-law-mul-Fin {succ-ℕ k} x y =
  ( commutative-mul-Fin x (neg-Fin y)) ∙
  ( ( left-negative-law-mul-Fin y x) ∙
    ( ap neg-Fin (commutative-mul-Fin y x)))

left-successor-law-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  Id (mul-Fin (succ-Fin x) y) (add-Fin y (mul-Fin x y))
left-successor-law-mul-Fin {succ-ℕ k} x y =
  ( ap (mul-Fin' y) (is-add-one-succ-Fin x)) ∙
  ( ( right-distributive-mul-add-Fin one-Fin x y) ∙
    ( ap (add-Fin' (mul-Fin x y)) (left-unit-law-mul-Fin y)))

right-successor-law-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  Id (mul-Fin x (succ-Fin y)) (add-Fin x (mul-Fin x y))
right-successor-law-mul-Fin {succ-ℕ k} x y =
  ( ap (mul-Fin x) (is-add-one-succ-Fin y)) ∙
  ( ( left-distributive-mul-add-Fin x one-Fin y) ∙
    ( ap (add-Fin' (mul-Fin x y)) (right-unit-law-mul-Fin x)))

left-predecessor-law-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  Id (mul-Fin (pred-Fin x) y) (add-Fin (neg-Fin y) (mul-Fin x y))
left-predecessor-law-mul-Fin {succ-ℕ k} x y =
  ( ap (mul-Fin' y) (is-add-neg-one-pred-Fin x)) ∙
  ( ( right-distributive-mul-add-Fin neg-one-Fin x y) ∙
    ( ap (add-Fin' (mul-Fin x y)) (inv (is-mul-neg-one-neg-Fin y))))

right-predecessor-law-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  Id (mul-Fin x (pred-Fin y)) (add-Fin (neg-Fin x) (mul-Fin x y))
right-predecessor-law-mul-Fin {succ-ℕ k} x y =
  ( ap (mul-Fin x) (is-add-neg-one-pred-Fin y)) ∙
  ( ( left-distributive-mul-add-Fin x neg-one-Fin y) ∙
    ( ap (add-Fin' (mul-Fin x y)) (inv (is-mul-neg-one-neg-Fin' x))))
```

```agda
leq-nat-mod-succ-ℕ :
  (k x : ℕ) → leq-ℕ (nat-Fin (mod-succ-ℕ k x)) x
leq-nat-mod-succ-ℕ k zero-ℕ =
  concatenate-eq-leq-ℕ zero-ℕ (is-zero-nat-zero-Fin {k}) (refl-leq-ℕ zero-ℕ)
leq-nat-mod-succ-ℕ k (succ-ℕ x) =
  transitive-leq-ℕ
    ( nat-Fin (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( leq-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x))
    ( leq-nat-mod-succ-ℕ k x)
```

## Decidability of division

```agda
is-decidable-div-ℕ : (d x : ℕ) → is-decidable (div-ℕ d x)
is-decidable-div-ℕ zero-ℕ x =
  is-decidable-iff
    ( div-eq-ℕ zero-ℕ x)
    ( inv ∘ (is-zero-div-zero-ℕ x))
    ( is-decidable-is-zero-ℕ' x)
is-decidable-div-ℕ (succ-ℕ d) x =
  is-decidable-iff
    ( div-is-zero-mod-succ-ℕ d x)
    ( is-zero-mod-succ-ℕ d x)
    ( is-decidable-is-zero-Fin (mod-succ-ℕ d x))

is-decidable-is-even-ℕ : (x : ℕ) → is-decidable (is-even-ℕ x)
is-decidable-is-even-ℕ x = is-decidable-div-ℕ 2 x

is-decidable-is-odd-ℕ : (x : ℕ) → is-decidable (is-odd-ℕ x)
is-decidable-is-odd-ℕ x = is-decidable-neg (is-decidable-is-even-ℕ x)
```

```agda
neg-neg-Fin :
  {k : ℕ} (x : Fin k) → Id (neg-Fin (neg-Fin x)) x
neg-neg-Fin {succ-ℕ k} x =
  ( inv (right-unit-law-add-Fin (neg-Fin (neg-Fin x)))) ∙
  ( ( ap (add-Fin (neg-Fin (neg-Fin x))) (inv (left-inverse-law-add-Fin x))) ∙
    ( ( inv (associative-add-Fin (neg-Fin (neg-Fin x)) (neg-Fin x) x)) ∙
      ( ( ap (add-Fin' x) (left-inverse-law-add-Fin (neg-Fin x))) ∙
        ( left-unit-law-add-Fin x))))

is-equiv-neg-Fin :
  {k : ℕ} → is-equiv (neg-Fin {k})
pr1 (pr1 is-equiv-neg-Fin) = neg-Fin
pr2 (pr1 is-equiv-neg-Fin) = neg-neg-Fin
pr1 (pr2 is-equiv-neg-Fin) = neg-Fin
pr2 (pr2 is-equiv-neg-Fin) = neg-neg-Fin

equiv-neg-Fin :
  {k : ℕ} → Fin k ≃ Fin k
pr1 equiv-neg-Fin = neg-Fin
pr2 equiv-neg-Fin = is-equiv-neg-Fin
```
