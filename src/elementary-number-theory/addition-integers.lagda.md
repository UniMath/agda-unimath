---
title: Univalent Mathematics in Agda
---

# Addition on the integers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.addition-integers where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; left-unit-law-add-ℕ; left-successor-law-add-ℕ)
open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap; ap-binary)
open import foundation.injective-maps using (is-injective)
open import elementary-number-theory.integers using
  ( ℤ; zero-ℤ; one-ℤ; neg-one-ℤ; succ-ℤ; pred-ℤ; isretr-pred-ℤ;
    issec-pred-ℤ; neg-ℤ; pred-neg-ℤ; neg-pred-ℤ; in-pos; in-neg;
    is-nonnegative-ℤ; is-nonnegative-succ-ℤ; is-positive-ℤ; is-positive-succ-ℤ;
    is-nonnegative-is-positive-ℤ; int-ℕ; succ-int-ℕ; is-zero-ℤ)
open import foundation.laws-for-operations using
  ( interchange-law; interchange-law-commutative-and-associative)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import foundation.unit-type using (star)
```

# Addition on the integers

We introduce addition on the integers and derive its basic properties with respect to `succ-ℤ` and `neg-ℤ`. Properties of addition with respect to inequality are derived in `inequality-integers`.

```agda
add-ℤ : ℤ → ℤ → ℤ
add-ℤ (inl zero-ℕ) l = pred-ℤ l
add-ℤ (inl (succ-ℕ x)) l = pred-ℤ (add-ℤ (inl x) l)
add-ℤ (inr (inl star)) l = l
add-ℤ (inr (inr zero-ℕ)) l = succ-ℤ l
add-ℤ (inr (inr (succ-ℕ x))) l = succ-ℤ (add-ℤ (inr (inr x)) l)

add-ℤ' : ℤ → ℤ → ℤ
add-ℤ' x y = add-ℤ y x

ap-add-ℤ :
  {x y x' y' : ℤ} → Id x x' → Id y y' → Id (add-ℤ x y) (add-ℤ x' y')
ap-add-ℤ p q = ap-binary add-ℤ p q
```

## Laws for addition on ℤ

```agda
abstract
  left-unit-law-add-ℤ :
    (k : ℤ) → Id (add-ℤ zero-ℤ k) k
  left-unit-law-add-ℤ k = refl
  
  right-unit-law-add-ℤ :
    (k : ℤ) → Id (add-ℤ k zero-ℤ) k
  right-unit-law-add-ℤ (inl zero-ℕ) = refl
  right-unit-law-add-ℤ (inl (succ-ℕ x)) =
    ap pred-ℤ (right-unit-law-add-ℤ (inl x))
  right-unit-law-add-ℤ (inr (inl star)) = refl
  right-unit-law-add-ℤ (inr (inr zero-ℕ)) = refl
  right-unit-law-add-ℤ (inr (inr (succ-ℕ x))) =
    ap succ-ℤ (right-unit-law-add-ℤ (inr (inr x)))

abstract
  left-predecessor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ (pred-ℤ x) y) (pred-ℤ (add-ℤ x y))
  left-predecessor-law-add-ℤ (inl n) y = refl
  left-predecessor-law-add-ℤ (inr (inl star)) y = refl
  left-predecessor-law-add-ℤ (inr (inr zero-ℕ)) y =
    ( ap (add-ℤ' y) (isretr-pred-ℤ zero-ℤ)) ∙ 
    ( inv (isretr-pred-ℤ y))
  left-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    ( ap (add-ℤ' y) (isretr-pred-ℤ (inr (inr x)))) ∙
    ( inv (isretr-pred-ℤ (add-ℤ (inr (inr x)) y)))

  right-predecessor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ x (pred-ℤ y)) (pred-ℤ (add-ℤ x y))
  right-predecessor-law-add-ℤ (inl zero-ℕ) n = refl
  right-predecessor-law-add-ℤ (inl (succ-ℕ m)) n =
    ap pred-ℤ (right-predecessor-law-add-ℤ (inl m) n)
  right-predecessor-law-add-ℤ (inr (inl star)) n = refl
  right-predecessor-law-add-ℤ (inr (inr zero-ℕ)) n =
    (issec-pred-ℤ n) ∙ (inv (isretr-pred-ℤ n))
  right-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) n =
    ( ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) n)) ∙
    ( ( issec-pred-ℤ (add-ℤ (inr (inr x)) n)) ∙ 
      ( inv (isretr-pred-ℤ (add-ℤ (inr (inr x)) n))))

abstract
  left-successor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ (succ-ℤ x) y) (succ-ℤ (add-ℤ x y))
  left-successor-law-add-ℤ (inl zero-ℕ) y =
    ( ap (add-ℤ' y) (issec-pred-ℤ zero-ℤ)) ∙
    ( inv (issec-pred-ℤ y))
  left-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    ( inv (issec-pred-ℤ (add-ℤ (inl x) y))) ∙
    ( ap succ-ℤ (inv (left-predecessor-law-add-ℤ (inl x) y)))
  left-successor-law-add-ℤ (inr (inl star)) y = refl
  left-successor-law-add-ℤ (inr (inr x)) y = refl

  right-successor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ x (succ-ℤ y)) (succ-ℤ (add-ℤ x y))
  right-successor-law-add-ℤ (inl zero-ℕ) y =
    (isretr-pred-ℤ y) ∙ (inv (issec-pred-ℤ y))
  right-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    ( ap pred-ℤ (right-successor-law-add-ℤ (inl x) y)) ∙
    ( ( isretr-pred-ℤ (add-ℤ (inl x) y)) ∙
      ( inv (issec-pred-ℤ (add-ℤ (inl x) y))))
  right-successor-law-add-ℤ (inr (inl star)) y = refl
  right-successor-law-add-ℤ (inr (inr zero-ℕ)) y = refl
  right-successor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    ap succ-ℤ (right-successor-law-add-ℤ (inr (inr x)) y)

abstract
  is-add-one-succ-ℤ' : (x : ℤ) → Id (succ-ℤ x) (add-ℤ x one-ℤ)
  is-add-one-succ-ℤ' x =
    inv (ap succ-ℤ (right-unit-law-add-ℤ x)) ∙
    inv (right-successor-law-add-ℤ x zero-ℤ)

  is-add-one-succ-ℤ : (x : ℤ) → Id (succ-ℤ x) (add-ℤ one-ℤ x)
  is-add-one-succ-ℤ x = inv (left-successor-law-add-ℤ zero-ℤ x)

  is-add-neg-one-pred-ℤ : (x : ℤ) → Id (pred-ℤ x) (add-ℤ neg-one-ℤ x)
  is-add-neg-one-pred-ℤ x =
    inv (left-predecessor-law-add-ℤ zero-ℤ x)

  is-add-neg-one-pred-ℤ' : (x : ℤ) → Id (pred-ℤ x) (add-ℤ x neg-one-ℤ)
  is-add-neg-one-pred-ℤ' x =
    inv (ap pred-ℤ (right-unit-law-add-ℤ x)) ∙
    inv (right-predecessor-law-add-ℤ x zero-ℤ)

abstract
  associative-add-ℤ :
    (x y z : ℤ) → Id (add-ℤ (add-ℤ x y) z) (add-ℤ x (add-ℤ y z))
  associative-add-ℤ (inl zero-ℕ) y z =
    ( ap (add-ℤ' z) (left-predecessor-law-add-ℤ zero-ℤ y)) ∙
    ( ( left-predecessor-law-add-ℤ y z) ∙
      ( inv (left-predecessor-law-add-ℤ zero-ℤ (add-ℤ y z))))
  associative-add-ℤ (inl (succ-ℕ x)) y z =
    ( ap (add-ℤ' z) (left-predecessor-law-add-ℤ (inl x) y)) ∙
    ( ( left-predecessor-law-add-ℤ (add-ℤ (inl x) y) z) ∙
      ( ( ap pred-ℤ (associative-add-ℤ (inl x) y z)) ∙ 
        ( inv (left-predecessor-law-add-ℤ (inl x) (add-ℤ y z)))))
  associative-add-ℤ (inr (inl star)) y z = refl
  associative-add-ℤ (inr (inr zero-ℕ)) y z =
    ( ap (add-ℤ' z) (left-successor-law-add-ℤ zero-ℤ y)) ∙ 
    ( ( left-successor-law-add-ℤ y z) ∙ 
      ( inv (left-successor-law-add-ℤ zero-ℤ (add-ℤ y z))))
  associative-add-ℤ (inr (inr (succ-ℕ x))) y z =
    ( ap (add-ℤ' z) (left-successor-law-add-ℤ (inr (inr x)) y)) ∙
    ( ( left-successor-law-add-ℤ (add-ℤ (inr (inr x)) y) z) ∙
      ( ( ap succ-ℤ (associative-add-ℤ (inr (inr x)) y z)) ∙
        ( inv (left-successor-law-add-ℤ (inr (inr x)) (add-ℤ y z)))))

abstract
  commutative-add-ℤ :
    (x y : ℤ) → Id (add-ℤ x y) (add-ℤ y x)
  commutative-add-ℤ (inl zero-ℕ) y =
    ( left-predecessor-law-add-ℤ zero-ℤ y) ∙
    ( inv
      ( ( right-predecessor-law-add-ℤ y zero-ℤ) ∙
        ( ap pred-ℤ (right-unit-law-add-ℤ y))))
  commutative-add-ℤ (inl (succ-ℕ x)) y =
    ( ap pred-ℤ (commutative-add-ℤ (inl x) y)) ∙ 
    ( inv (right-predecessor-law-add-ℤ y (inl x)))
  commutative-add-ℤ (inr (inl star)) y = inv (right-unit-law-add-ℤ y)
  commutative-add-ℤ (inr (inr zero-ℕ)) y =
    inv
      ( ( right-successor-law-add-ℤ y zero-ℤ) ∙
        ( ap succ-ℤ (right-unit-law-add-ℤ y)))
  commutative-add-ℤ (inr (inr (succ-ℕ x))) y =
    ( ap succ-ℤ (commutative-add-ℤ (inr (inr x)) y)) ∙ 
    ( inv (right-successor-law-add-ℤ y (inr (inr x))))

abstract
  left-inverse-law-add-ℤ :
    (x : ℤ) → Id (add-ℤ (neg-ℤ x) x) zero-ℤ
  left-inverse-law-add-ℤ (inl zero-ℕ) = refl
  left-inverse-law-add-ℤ (inl (succ-ℕ x)) =
    ( ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) (inl x))) ∙ 
    ( ( issec-pred-ℤ (add-ℤ (inr (inr x)) (inl x))) ∙
      ( left-inverse-law-add-ℤ (inl x))) 
  left-inverse-law-add-ℤ (inr (inl star)) = refl
  left-inverse-law-add-ℤ (inr (inr x)) =
    ( commutative-add-ℤ (inl x) (inr (inr x))) ∙ 
    ( left-inverse-law-add-ℤ (inl x))
  
  right-inverse-law-add-ℤ :
    (x : ℤ) → Id (add-ℤ x (neg-ℤ x)) zero-ℤ
  right-inverse-law-add-ℤ x =
    ( commutative-add-ℤ x (neg-ℤ x)) ∙ (left-inverse-law-add-ℤ x)

issec-add-neg-ℤ :
  (x y : ℤ) → Id (add-ℤ x (add-ℤ (neg-ℤ x) y)) y
issec-add-neg-ℤ x y =
  ( inv (associative-add-ℤ x (neg-ℤ x) y)) ∙
  ( ap (add-ℤ' y) (right-inverse-law-add-ℤ x))

isretr-add-neg-ℤ :
  (x y : ℤ) → Id (add-ℤ (neg-ℤ x) (add-ℤ x y)) y
isretr-add-neg-ℤ x y =
  ( inv (associative-add-ℤ (neg-ℤ x) x y)) ∙
  ( ap (add-ℤ' y) (left-inverse-law-add-ℤ x))

issec-add-neg-ℤ' :
  (x y : ℤ) → Id (add-ℤ' x (add-ℤ' (neg-ℤ x) y)) y
issec-add-neg-ℤ' x y =
  ( associative-add-ℤ y (neg-ℤ x) x) ∙
  ( ( ap (add-ℤ y) (left-inverse-law-add-ℤ x)) ∙
    ( right-unit-law-add-ℤ y))

isretr-add-neg-ℤ' :
  (x y : ℤ) → Id (add-ℤ' (neg-ℤ x) (add-ℤ' x y)) y
isretr-add-neg-ℤ' x y =
  ( associative-add-ℤ y x (neg-ℤ x)) ∙
  ( ( ap (add-ℤ y) (right-inverse-law-add-ℤ x)) ∙
    ( right-unit-law-add-ℤ y))

interchange-law-add-add-ℤ : interchange-law add-ℤ add-ℤ
interchange-law-add-add-ℤ =
  interchange-law-commutative-and-associative
    add-ℤ
    commutative-add-ℤ
    associative-add-ℤ

is-injective-add-ℤ' : (x : ℤ) → is-injective (add-ℤ' x)
is-injective-add-ℤ' x {y} {z} p =
  ( inv (isretr-add-neg-ℤ' x y)) ∙
  ( ( ap (add-ℤ' (neg-ℤ x)) p) ∙
    ( isretr-add-neg-ℤ' x z))

is-injective-add-ℤ : (x : ℤ) → is-injective (add-ℤ x)
is-injective-add-ℤ x {y} {z} p =
  ( inv (isretr-add-neg-ℤ x y)) ∙
  ( ( ap (add-ℤ (neg-ℤ x)) p) ∙
    ( isretr-add-neg-ℤ x z))
```

```agda
right-negative-law-add-ℤ :
  (k l : ℤ) → Id (add-ℤ k (neg-ℤ l)) (neg-ℤ (add-ℤ (neg-ℤ k) l))
right-negative-law-add-ℤ (inl zero-ℕ) l =
  ( left-predecessor-law-add-ℤ zero-ℤ (neg-ℤ l)) ∙
  ( pred-neg-ℤ l)
right-negative-law-add-ℤ (inl (succ-ℕ x)) l =
  ( left-predecessor-law-add-ℤ (inl x) (neg-ℤ l)) ∙
  ( ( ap pred-ℤ (right-negative-law-add-ℤ (inl x) l)) ∙
    ( pred-neg-ℤ (add-ℤ (inr (inr x)) l)))
right-negative-law-add-ℤ (inr (inl star)) l = refl
right-negative-law-add-ℤ (inr (inr zero-ℕ)) l = inv (neg-pred-ℤ l)
right-negative-law-add-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-successor-law-add-ℤ (in-pos n) (neg-ℤ l)) ∙
  ( ( ap succ-ℤ (right-negative-law-add-ℤ (inr (inr n)) l)) ∙
    ( inv (neg-pred-ℤ (add-ℤ (inl n) l))))

distributive-neg-add-ℤ :
  (k l : ℤ) → Id (neg-ℤ (add-ℤ k l)) (add-ℤ (neg-ℤ k) (neg-ℤ l))
distributive-neg-add-ℤ (inl zero-ℕ) l =
  ( ap neg-ℤ (left-predecessor-law-add-ℤ zero-ℤ l)) ∙
  ( neg-pred-ℤ l)
distributive-neg-add-ℤ (inl (succ-ℕ n)) l =
  ( neg-pred-ℤ (add-ℤ (inl n) l)) ∙
  ( ( ap succ-ℤ (distributive-neg-add-ℤ (inl n) l)) ∙
    ( ap (add-ℤ' (neg-ℤ l)) (inv (neg-pred-ℤ (inl n)))))
distributive-neg-add-ℤ (inr (inl star)) l = refl
distributive-neg-add-ℤ (inr (inr zero-ℕ)) l = inv (pred-neg-ℤ l)
distributive-neg-add-ℤ (inr (inr (succ-ℕ n))) l =
  ( inv (pred-neg-ℤ (add-ℤ (in-pos n) l))) ∙
  ( ap pred-ℤ (distributive-neg-add-ℤ (inr (inr n)) l))
```

```agda
negatives-add-ℤ :
  (x y : ℕ) → Id (add-ℤ (in-neg x) (in-neg y)) (in-neg (succ-ℕ (add-ℕ x y)))
negatives-add-ℤ zero-ℕ y = ap (inl ∘ succ-ℕ) (inv (left-unit-law-add-ℕ y))
negatives-add-ℤ (succ-ℕ x) y =
  ( ap pred-ℤ (negatives-add-ℤ x y)) ∙
  ( ap (inl ∘ succ-ℕ) (inv (left-successor-law-add-ℕ x y)))

add-one-left-ℤ :
  (x : ℤ) → Id (add-ℤ one-ℤ x) (succ-ℤ x)
add-one-left-ℤ x = refl

add-one-right-ℤ :
  (x : ℤ) → Id (add-ℤ x one-ℤ) (succ-ℤ x)
add-one-right-ℤ x = commutative-add-ℤ x one-ℤ

add-neg-one-left-ℤ :
  (x : ℤ) → Id (add-ℤ neg-one-ℤ x) (pred-ℤ x)
add-neg-one-left-ℤ x = refl

add-neg-one-right-ℤ :
  (x : ℤ) → Id (add-ℤ x neg-one-ℤ) (pred-ℤ x)
add-neg-one-right-ℤ x = commutative-add-ℤ x neg-one-ℤ
```

```agda
is-nonnegative-add-ℤ :
  (k l : ℤ) →
  is-nonnegative-ℤ k → is-nonnegative-ℤ l → is-nonnegative-ℤ (add-ℤ k l)
is-nonnegative-add-ℤ (inr (inl star)) (inr (inl star)) p q = star
is-nonnegative-add-ℤ (inr (inl star)) (inr (inr n)) p q = star
is-nonnegative-add-ℤ (inr (inr zero-ℕ)) (inr (inl star)) p q = star
is-nonnegative-add-ℤ (inr (inr (succ-ℕ n))) (inr (inl star)) star star =
  is-nonnegative-succ-ℤ
    ( add-ℤ (inr (inr n)) (inr (inl star)))
    ( is-nonnegative-add-ℤ (inr (inr n)) (inr (inl star)) star star)
is-nonnegative-add-ℤ (inr (inr zero-ℕ)) (inr (inr m)) star star = star
is-nonnegative-add-ℤ (inr (inr (succ-ℕ n))) (inr (inr m)) star star =
  is-nonnegative-succ-ℤ
    ( add-ℤ (inr (inr n)) (inr (inr m)))
    ( is-nonnegative-add-ℤ (inr (inr n)) (inr (inr m)) star star)
```

```agda
is-positive-add-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (add-ℤ x y)
is-positive-add-ℤ {inr (inr zero-ℕ)} {inr (inr y)} H K = star
is-positive-add-ℤ {inr (inr (succ-ℕ x))} {inr (inr y)} H K =
  is-positive-succ-ℤ
    ( is-nonnegative-is-positive-ℤ
      ( is-positive-add-ℤ {inr (inr x)} {inr (inr y)} star star))
```

```agda
add-int-ℕ : (x y : ℕ) → Id (add-ℤ (int-ℕ x) (int-ℕ y)) (int-ℕ (add-ℕ x y))
add-int-ℕ x zero-ℕ = right-unit-law-add-ℤ (int-ℕ x)
add-int-ℕ x (succ-ℕ y) =
  ( ap (add-ℤ (int-ℕ x)) (inv (succ-int-ℕ y))) ∙
  ( ( right-successor-law-add-ℤ (int-ℕ x) (int-ℕ y)) ∙
    ( ( ap succ-ℤ (add-int-ℕ x y)) ∙
      ( succ-int-ℕ (add-ℕ x y))))
```

```agda
is-zero-add-ℤ :
  (x y : ℤ) → Id (add-ℤ x y) y → is-zero-ℤ x
is-zero-add-ℤ x y H =
  ( inv (right-unit-law-add-ℤ x)) ∙
  ( ( inv (ap (add-ℤ x) (right-inverse-law-add-ℤ y))) ∙
    ( ( inv (associative-add-ℤ x y (neg-ℤ y))) ∙
      ( ( ap (add-ℤ' (neg-ℤ y)) H) ∙
        ( right-inverse-law-add-ℤ y))))

is-zero-add-ℤ' :
  (x y : ℤ) → Id (add-ℤ x y) x → is-zero-ℤ y
is-zero-add-ℤ' x y H =
  is-zero-add-ℤ y x (commutative-add-ℤ y x ∙ H)
```

```agda
abstract
  is-equiv-add-ℤ : (x : ℤ) → is-equiv (add-ℤ x)
  pr1 (pr1 (is-equiv-add-ℤ x)) = add-ℤ (neg-ℤ x)
  pr2 (pr1 (is-equiv-add-ℤ x)) y =
    ( inv (associative-add-ℤ x (neg-ℤ x) y)) ∙
    ( ( ap (add-ℤ' y) (right-inverse-law-add-ℤ x)) ∙
      ( left-unit-law-add-ℤ y))
  pr1 (pr2 (is-equiv-add-ℤ x)) = add-ℤ (neg-ℤ x)
  pr2 (pr2 (is-equiv-add-ℤ x)) y =
    ( inv (associative-add-ℤ (neg-ℤ x) x y)) ∙
    ( ( ap (add-ℤ' y) (left-inverse-law-add-ℤ x)) ∙
      ( left-unit-law-add-ℤ y))

equiv-add-ℤ : ℤ → (ℤ ≃ ℤ)
pr1 (equiv-add-ℤ x) = add-ℤ x
pr2 (equiv-add-ℤ x) = is-equiv-add-ℤ x

abstract
  is-equiv-add-ℤ' : (y : ℤ) → is-equiv (add-ℤ' y)
  pr1 (pr1 (is-equiv-add-ℤ' y)) = add-ℤ' (neg-ℤ y)
  pr2 (pr1 (is-equiv-add-ℤ' y)) x =
    ( associative-add-ℤ x (neg-ℤ y) y) ∙
    ( ( ap (add-ℤ x) (left-inverse-law-add-ℤ y)) ∙
      ( right-unit-law-add-ℤ x))
  pr1 (pr2 (is-equiv-add-ℤ' y)) = add-ℤ' (neg-ℤ y)
  pr2 (pr2 (is-equiv-add-ℤ' y)) x =
    ( associative-add-ℤ x y (neg-ℤ y)) ∙
    ( ( ap (add-ℤ x) (right-inverse-law-add-ℤ y)) ∙
      ( right-unit-law-add-ℤ x))

equiv-add-ℤ' : ℤ → (ℤ ≃ ℤ)
pr1 (equiv-add-ℤ' y) = add-ℤ' y
pr2 (equiv-add-ℤ' y) = is-equiv-add-ℤ' y
```
