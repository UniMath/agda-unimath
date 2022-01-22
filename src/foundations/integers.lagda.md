---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.integers where

open import foundations.addition-natural-numbers using
  (add-ℕ; left-unit-law-add-ℕ; left-successor-law-add-ℕ)  
open import foundations.coproduct-types using (coprod; inl; inr) public
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.empty-type using (empty; ex-falso)
open import foundations.functions using (id; _∘_)
open import foundations.identity-types using (Id; refl; _∙_; inv; ap; ap-binary)
open import foundations.injective-maps using (is-injective)
open import foundations.laws-for-operations using
  ( interchange-law; interchange-law-commutative-and-associative)
open import foundations.levels using (UU; Level; lzero)
open import foundations.multiplication-natural-numbers using (mul-ℕ)
open import foundations.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; Eq-ℕ; refl-Eq-ℕ; eq-Eq-ℕ; is-nonzero-ℕ)
open import foundations.negation using (¬)
open import foundations.unit-type using (unit; star)
```

## The type of integers

```agda
ℤ : UU lzero
ℤ = coprod ℕ (coprod unit ℕ)
```

### Observational equality on ℤ

```agda
Eq-ℤ : ℤ → ℤ → UU lzero
Eq-ℤ (inl x) (inl y) = Eq-ℕ x y
Eq-ℤ (inl x) (inr y) = empty
Eq-ℤ (inr x) (inl y) = empty
Eq-ℤ (inr (inl x)) (inr (inl y)) = unit
Eq-ℤ (inr (inl x)) (inr (inr y)) = empty
Eq-ℤ (inr (inr x)) (inr (inl y)) = empty
Eq-ℤ (inr (inr x)) (inr (inr y)) = Eq-ℕ x y

refl-Eq-ℤ : (x : ℤ) → Eq-ℤ x x
refl-Eq-ℤ (inl x) = refl-Eq-ℕ x
refl-Eq-ℤ (inr (inl x)) = star
refl-Eq-ℤ (inr (inr x)) = refl-Eq-ℕ x

Eq-eq-ℤ : {x y : ℤ} → Id x y → Eq-ℤ x y
Eq-eq-ℤ {x} {.x} refl = refl-Eq-ℤ x

eq-Eq-ℤ : (x y : ℤ) → Eq-ℤ x y → Id x y
eq-Eq-ℤ (inl x) (inl y) e = ap inl (eq-Eq-ℕ x y e)
eq-Eq-ℤ (inr (inl star)) (inr (inl star)) e = refl
eq-Eq-ℤ (inr (inr x)) (inr (inr y)) e = ap (inr ∘ inr) (eq-Eq-ℕ x y e)
```

## Inclusion of the negative integers

```agda
in-neg : ℕ → ℤ
in-neg n = inl n

neg-one-ℤ : ℤ
neg-one-ℤ = in-neg zero-ℕ

is-neg-one-ℤ : ℤ → UU lzero
is-neg-one-ℤ x = Id x neg-one-ℤ
```

## Zero

```agda
zero-ℤ : ℤ
zero-ℤ = inr (inl star)

is-zero-ℤ : ℤ → UU lzero
is-zero-ℤ x = Id x zero-ℤ

is-nonzero-ℤ : ℤ → UU lzero
is-nonzero-ℤ k = ¬ (is-zero-ℤ k)
```

## Inclusion of the positive integers

```agda
in-pos : ℕ → ℤ
in-pos n = inr (inr n)

one-ℤ : ℤ
one-ℤ = in-pos zero-ℕ

is-one-ℤ : ℤ → UU lzero
is-one-ℤ x = Id x one-ℤ
```

- Inclusion of the natural numbers

```agda
int-ℕ : ℕ → ℤ
int-ℕ zero-ℕ = zero-ℤ
int-ℕ (succ-ℕ n) = in-pos n

is-injective-int-ℕ : is-injective int-ℕ
is-injective-int-ℕ {zero-ℕ} {zero-ℕ} refl = refl
is-injective-int-ℕ {succ-ℕ x} {succ-ℕ y} refl = refl

is-nonzero-int-ℕ : (n : ℕ) → is-nonzero-ℕ n → is-nonzero-ℤ (int-ℕ n)
is-nonzero-int-ℕ zero-ℕ H p = H refl
```

- Induction principle on the type of integers

```agda
ind-ℤ :
  {l : Level} (P : ℤ → UU l) →
  P neg-one-ℤ → ((n : ℕ) → P (inl n) → P (inl (succ-ℕ n))) →
  P zero-ℤ →
  P one-ℤ → ((n : ℕ) → P (inr (inr (n))) → P (inr (inr (succ-ℕ n)))) →
  (k : ℤ) → P k
ind-ℤ P p-1 p-S p0 p1 pS (inl zero-ℕ) = p-1
ind-ℤ P p-1 p-S p0 p1 pS (inl (succ-ℕ x)) =
  p-S x (ind-ℤ P p-1 p-S p0 p1 pS (inl x))
ind-ℤ P p-1 p-S p0 p1 pS (inr (inl star)) = p0
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr zero-ℕ)) = p1
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (succ-ℕ x))) =
  pS x (ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (x))))
```

- The successor and predecessor functions on ℤ

```agda
succ-ℤ : ℤ → ℤ
succ-ℤ (inl zero-ℕ) = zero-ℤ
succ-ℤ (inl (succ-ℕ x)) = inl x
succ-ℤ (inr (inl star)) = one-ℤ
succ-ℤ (inr (inr x)) = inr (inr (succ-ℕ x))

pred-ℤ : ℤ → ℤ
pred-ℤ (inl x) = inl (succ-ℕ x)
pred-ℤ (inr (inl star)) = inl zero-ℕ
pred-ℤ (inr (inr zero-ℕ)) = inr (inl star)
pred-ℤ (inr (inr (succ-ℕ x))) = inr (inr x)
```

### Arithmetic operations on the integers

- Addition on ℤ

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

- The negative of an integer

```agda
neg-ℤ : ℤ → ℤ
neg-ℤ (inl x) = inr (inr x)
neg-ℤ (inr (inl star)) = inr (inl star)
neg-ℤ (inr (inr x)) = inl x
```

- Multiplication of integers

We give two definitions of multiplication on ℤ

```agda
mul-ℤ : ℤ → ℤ → ℤ
mul-ℤ (inl zero-ℕ) l = neg-ℤ l
mul-ℤ (inl (succ-ℕ x)) l = add-ℤ (neg-ℤ l) (mul-ℤ (inl x) l)
mul-ℤ (inr (inl star)) l = zero-ℤ
mul-ℤ (inr (inr zero-ℕ)) l = l
mul-ℤ (inr (inr (succ-ℕ x))) l = add-ℤ l (mul-ℤ (inr (inr x)) l)

mul-ℤ' : ℤ → ℤ → ℤ
mul-ℤ' x y = mul-ℤ y x

ap-mul-ℤ :
  {x y x' y' : ℤ} → Id x x' → Id y y' → Id (mul-ℤ x y) (mul-ℤ x' y')
ap-mul-ℤ p q = ap-binary mul-ℤ p q

explicit-mul-ℤ : ℤ → ℤ → ℤ
explicit-mul-ℤ (inl x) (inl y) = int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y))
explicit-mul-ℤ (inl x) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inl x) (inr (inr y)) =
  neg-ℤ (int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)))
explicit-mul-ℤ (inr (inl star)) (inl y) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inl y) =
  neg-ℤ (int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)))
explicit-mul-ℤ (inr (inl star)) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inr (inl star)) (inr (inr y)) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inr (inr y)) = int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y))

explicit-mul-ℤ' : ℤ → ℤ → ℤ
explicit-mul-ℤ' x y = explicit-mul-ℤ y x
```

## The successor and predecessor functions on ℤ are mutual inverses

```agda
abstract
  isretr-pred-ℤ :
    (k : ℤ) → Id (pred-ℤ (succ-ℤ k)) k
  isretr-pred-ℤ (inl zero-ℕ) = refl
  isretr-pred-ℤ (inl (succ-ℕ x)) = refl
  isretr-pred-ℤ (inr (inl star)) = refl
  isretr-pred-ℤ (inr (inr zero-ℕ)) = refl
  isretr-pred-ℤ (inr (inr (succ-ℕ x))) = refl
  
  issec-pred-ℤ :
    (k : ℤ) → Id (succ-ℤ (pred-ℤ k)) k
  issec-pred-ℤ (inl zero-ℕ) = refl
  issec-pred-ℤ (inl (succ-ℕ x)) = refl
  issec-pred-ℤ (inr (inl star)) = refl
  issec-pred-ℤ (inr (inr zero-ℕ)) = refl
  issec-pred-ℤ (inr (inr (succ-ℕ x))) = refl
```

### The successor function on ℤ is injective

```agda
  is-injective-succ-ℤ : is-injective succ-ℤ
  is-injective-succ-ℤ {x} {y} p =
    inv (isretr-pred-ℤ x) ∙ (ap pred-ℤ p ∙ isretr-pred-ℤ y)
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

## Laws for multiplication on ℤ

```agda
left-zero-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ zero-ℤ k) zero-ℤ
left-zero-law-mul-ℤ k = refl

right-zero-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ k zero-ℤ) zero-ℤ
right-zero-law-mul-ℤ (inl zero-ℕ) = refl
right-zero-law-mul-ℤ (inl (succ-ℕ n)) =
  right-zero-law-mul-ℤ (inl n)
right-zero-law-mul-ℤ (inr (inl star)) = refl
right-zero-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-zero-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  right-zero-law-mul-ℤ (inr (inr n))

left-unit-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ one-ℤ k) k
left-unit-law-mul-ℤ k = refl

right-unit-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ k one-ℤ) k
right-unit-law-mul-ℤ (inl zero-ℕ) = refl
right-unit-law-mul-ℤ (inl (succ-ℕ n)) =
  ap (add-ℤ (neg-one-ℤ)) (right-unit-law-mul-ℤ (inl n))
right-unit-law-mul-ℤ (inr (inl star)) = refl
right-unit-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  ap (add-ℤ one-ℤ) (right-unit-law-mul-ℤ (inr (inr n)))

neg-neg-ℤ : (k : ℤ) → Id (neg-ℤ (neg-ℤ k)) k
neg-neg-ℤ (inl n) = refl
neg-neg-ℤ (inr (inl star)) = refl
neg-neg-ℤ (inr (inr n)) = refl

neg-pred-ℤ : (k : ℤ) → Id (neg-ℤ (pred-ℤ k)) (succ-ℤ (neg-ℤ k))
neg-pred-ℤ (inl x) = refl
neg-pred-ℤ (inr (inl star)) = refl
neg-pred-ℤ (inr (inr zero-ℕ)) = refl
neg-pred-ℤ (inr (inr (succ-ℕ x))) = refl

neg-succ-ℤ : (x : ℤ) → Id (neg-ℤ (succ-ℤ x)) (pred-ℤ (neg-ℤ x))
neg-succ-ℤ (inl zero-ℕ) = refl
neg-succ-ℤ (inl (succ-ℕ x)) = refl
neg-succ-ℤ (inr (inl star)) = refl
neg-succ-ℤ (inr (inr x)) = refl

pred-neg-ℤ :
  (k : ℤ) → Id (pred-ℤ (neg-ℤ k)) (neg-ℤ (succ-ℤ k))
pred-neg-ℤ (inl zero-ℕ) = refl
pred-neg-ℤ (inl (succ-ℕ x)) = refl
pred-neg-ℤ (inr (inl star)) = refl
pred-neg-ℤ (inr (inr x)) = refl

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

left-neg-unit-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ neg-one-ℤ k) (neg-ℤ k)
left-neg-unit-law-mul-ℤ k = refl

right-neg-unit-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ k neg-one-ℤ) (neg-ℤ k)
right-neg-unit-law-mul-ℤ (inl zero-ℕ) = refl
right-neg-unit-law-mul-ℤ (inl (succ-ℕ n)) =
  ap (add-ℤ one-ℤ) (right-neg-unit-law-mul-ℤ (inl n))
right-neg-unit-law-mul-ℤ (inr (inl star)) = refl
right-neg-unit-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-neg-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  ap (add-ℤ neg-one-ℤ) (right-neg-unit-law-mul-ℤ (inr (inr n)))

left-successor-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ (succ-ℤ k) l) (add-ℤ l (mul-ℤ k l))
left-successor-law-mul-ℤ (inl zero-ℕ) l =
  inv (right-inverse-law-add-ℤ l)
left-successor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( ( inv (left-unit-law-add-ℤ (mul-ℤ (inl n) l))) ∙
    ( ap
      ( add-ℤ' (mul-ℤ (inl n) l))
      ( inv (right-inverse-law-add-ℤ l)))) ∙
  ( associative-add-ℤ l (neg-ℤ l) (mul-ℤ (inl n) l))
left-successor-law-mul-ℤ (inr (inl star)) l =
  inv (right-unit-law-add-ℤ l)
left-successor-law-mul-ℤ (inr (inr n)) l = refl

left-predecessor-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ (pred-ℤ k) l) (add-ℤ (neg-ℤ l) (mul-ℤ k l))
left-predecessor-law-mul-ℤ (inl n) l = refl
left-predecessor-law-mul-ℤ (inr (inl star)) l =
  ( left-neg-unit-law-mul-ℤ l) ∙
  ( inv (right-unit-law-add-ℤ (neg-ℤ l)))
left-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l =
  inv (left-inverse-law-add-ℤ l)
left-predecessor-law-mul-ℤ (inr (inr (succ-ℕ x))) l =
   ( ap
     ( add-ℤ' (mul-ℤ (in-pos x) l))
     ( inv (left-inverse-law-add-ℤ l))) ∙
   ( associative-add-ℤ (neg-ℤ l) l (mul-ℤ (in-pos x) l))

right-successor-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ k (succ-ℤ l)) (add-ℤ k (mul-ℤ k l))
right-successor-law-mul-ℤ (inl zero-ℕ) l = inv (pred-neg-ℤ l)
right-successor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( left-predecessor-law-mul-ℤ (inl n) (succ-ℤ l)) ∙
  ( ( ap (add-ℤ (neg-ℤ (succ-ℤ l))) (right-successor-law-mul-ℤ (inl n) l)) ∙
    ( ( inv (associative-add-ℤ (neg-ℤ (succ-ℤ l)) (inl n) (mul-ℤ (inl n) l))) ∙
      ( ( ap
          ( add-ℤ' (mul-ℤ (inl n) l))
          { x = add-ℤ (neg-ℤ (succ-ℤ l)) (inl n)}
          { y = add-ℤ (inl (succ-ℕ n)) (neg-ℤ l)}
          ( ( right-successor-law-add-ℤ (neg-ℤ (succ-ℤ l)) (inl (succ-ℕ n))) ∙
            ( ( ap succ-ℤ
                ( commutative-add-ℤ (neg-ℤ (succ-ℤ l)) (inl (succ-ℕ n)))) ∙
              ( ( inv
                  ( right-successor-law-add-ℤ
                    ( inl (succ-ℕ n))
                    ( neg-ℤ (succ-ℤ l)))) ∙
                ( ap
                  ( add-ℤ (inl (succ-ℕ n)))
                  ( ( ap succ-ℤ (inv (pred-neg-ℤ l))) ∙
                    ( issec-pred-ℤ (neg-ℤ l)))))))) ∙
        ( associative-add-ℤ (inl (succ-ℕ n)) (neg-ℤ l) (mul-ℤ (inl n) l)))))
right-successor-law-mul-ℤ (inr (inl star)) l = refl
right-successor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
right-successor-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-successor-law-mul-ℤ (in-pos n) (succ-ℤ l)) ∙
  ( ( ap (add-ℤ (succ-ℤ l)) (right-successor-law-mul-ℤ (inr (inr n)) l)) ∙
    ( ( inv (associative-add-ℤ (succ-ℤ l) (in-pos n) (mul-ℤ (in-pos n) l))) ∙
      ( ( ap
          ( add-ℤ' (mul-ℤ (in-pos n) l))
          { x = add-ℤ (succ-ℤ l) (in-pos n)}
          { y = add-ℤ (in-pos (succ-ℕ n)) l}
          ( ( left-successor-law-add-ℤ l (in-pos n)) ∙
            ( ( ap succ-ℤ (commutative-add-ℤ l (in-pos n))) ∙
              ( inv (left-successor-law-add-ℤ (in-pos n) l))))) ∙
        ( associative-add-ℤ (inr (inr (succ-ℕ n))) l (mul-ℤ (inr (inr n)) l)))))

right-predecessor-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ k (pred-ℤ l)) (add-ℤ (neg-ℤ k) (mul-ℤ k l))
right-predecessor-law-mul-ℤ (inl zero-ℕ) l =
  ( left-neg-unit-law-mul-ℤ (pred-ℤ l)) ∙
  ( neg-pred-ℤ l)
right-predecessor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( left-predecessor-law-mul-ℤ (inl n) (pred-ℤ l)) ∙
  ( ( ap (add-ℤ (neg-ℤ (pred-ℤ l))) (right-predecessor-law-mul-ℤ (inl n) l)) ∙
    ( ( inv
        ( associative-add-ℤ (neg-ℤ (pred-ℤ l)) (in-pos n) (mul-ℤ (inl n) l))) ∙
      ( ( ap
          ( add-ℤ' (mul-ℤ (inl n) l))
          { x = add-ℤ (neg-ℤ (pred-ℤ l)) (inr (inr n))}
          { y = add-ℤ (neg-ℤ (inl (succ-ℕ n))) (neg-ℤ l)}
          ( ( ap (add-ℤ' (in-pos n)) (neg-pred-ℤ l)) ∙
            ( ( left-successor-law-add-ℤ (neg-ℤ l) (in-pos n)) ∙
              ( ( ap succ-ℤ (commutative-add-ℤ (neg-ℤ l) (in-pos n))) ∙
                ( inv (left-successor-law-add-ℤ (in-pos n) (neg-ℤ l))))))) ∙
        ( associative-add-ℤ (in-pos (succ-ℕ n)) (neg-ℤ l) (mul-ℤ (inl n) l)))))
right-predecessor-law-mul-ℤ (inr (inl star)) l = refl
right-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
right-predecessor-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-successor-law-mul-ℤ (in-pos n) (pred-ℤ l)) ∙
  ( ( ap (add-ℤ (pred-ℤ l)) (right-predecessor-law-mul-ℤ (inr (inr n)) l)) ∙
    ( ( inv (associative-add-ℤ (pred-ℤ l) (inl n) (mul-ℤ (inr (inr n)) l))) ∙
      ( ( ap
          ( add-ℤ' (mul-ℤ (in-pos n) l))
          { x = add-ℤ (pred-ℤ l) (inl n)}
          { y = add-ℤ (neg-ℤ (in-pos (succ-ℕ n))) l}
          ( ( left-predecessor-law-add-ℤ l (inl n)) ∙
            ( ( ap pred-ℤ (commutative-add-ℤ l (inl n))) ∙
              ( inv (left-predecessor-law-add-ℤ (inl n) l))))) ∙
        ( associative-add-ℤ (inl (succ-ℕ n)) l (mul-ℤ (inr (inr n)) l)))))

right-distributive-mul-add-ℤ :
  (k l m : ℤ) → Id (mul-ℤ (add-ℤ k l) m) (add-ℤ (mul-ℤ k m) (mul-ℤ l m))
right-distributive-mul-add-ℤ (inl zero-ℕ) l m =
  ( left-predecessor-law-mul-ℤ l m) ∙
  ( ap
    ( add-ℤ' (mul-ℤ l m))
    ( inv
      ( ( left-predecessor-law-mul-ℤ zero-ℤ m) ∙
        ( right-unit-law-add-ℤ (neg-ℤ m)))))
right-distributive-mul-add-ℤ (inl (succ-ℕ x)) l m =
  ( left-predecessor-law-mul-ℤ (add-ℤ (inl x) l) m) ∙
  ( ( ap (add-ℤ (neg-ℤ m)) (right-distributive-mul-add-ℤ (inl x) l m)) ∙
    ( inv (associative-add-ℤ (neg-ℤ m) (mul-ℤ (inl x) m) (mul-ℤ l m))))
right-distributive-mul-add-ℤ (inr (inl star)) l m = refl
right-distributive-mul-add-ℤ (inr (inr zero-ℕ)) l m =
  left-successor-law-mul-ℤ l m
right-distributive-mul-add-ℤ (inr (inr (succ-ℕ n))) l m =
  ( left-successor-law-mul-ℤ (add-ℤ (in-pos n) l) m) ∙
  ( ( ap (add-ℤ m) (right-distributive-mul-add-ℤ (inr (inr n)) l m)) ∙
    ( inv (associative-add-ℤ m (mul-ℤ (in-pos n) m) (mul-ℤ l m))))

left-negative-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ (neg-ℤ k) l) (neg-ℤ (mul-ℤ k l))
left-negative-law-mul-ℤ (inl zero-ℕ) l =
  ( left-unit-law-mul-ℤ l) ∙
  ( inv (neg-neg-ℤ l))
left-negative-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( ap (mul-ℤ' l) (neg-pred-ℤ (inl n))) ∙
  ( ( left-successor-law-mul-ℤ (neg-ℤ (inl n)) l) ∙
    ( ( ap (add-ℤ l) (left-negative-law-mul-ℤ (inl n) l)) ∙
      ( right-negative-law-add-ℤ l (mul-ℤ (inl n) l))))
left-negative-law-mul-ℤ (inr (inl star)) l = refl
left-negative-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
left-negative-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-predecessor-law-mul-ℤ (inl n) l) ∙
  ( ( ap (add-ℤ (neg-ℤ l)) (left-negative-law-mul-ℤ (inr (inr n)) l)) ∙
    ( inv (distributive-neg-add-ℤ l (mul-ℤ (in-pos n) l))))

associative-mul-ℤ :
  (k l m : ℤ) → Id (mul-ℤ (mul-ℤ k l) m) (mul-ℤ k (mul-ℤ l m))
associative-mul-ℤ (inl zero-ℕ) l m =
  left-negative-law-mul-ℤ l m
associative-mul-ℤ (inl (succ-ℕ n)) l m =
  ( right-distributive-mul-add-ℤ (neg-ℤ l) (mul-ℤ (inl n) l) m) ∙
  ( ( ap (add-ℤ (mul-ℤ (neg-ℤ l) m)) (associative-mul-ℤ (inl n) l m)) ∙
    ( ap
      ( add-ℤ' (mul-ℤ (inl n) (mul-ℤ l m)))
      ( left-negative-law-mul-ℤ l m)))
associative-mul-ℤ (inr (inl star)) l m = refl
associative-mul-ℤ (inr (inr zero-ℕ)) l m = refl
associative-mul-ℤ (inr (inr (succ-ℕ n))) l m =
  ( right-distributive-mul-add-ℤ l (mul-ℤ (in-pos n) l) m) ∙
  ( ap (add-ℤ (mul-ℤ l m)) (associative-mul-ℤ (inr (inr n)) l m))

commutative-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ k l) (mul-ℤ l k)
commutative-mul-ℤ (inl zero-ℕ) l = inv (right-neg-unit-law-mul-ℤ l)
commutative-mul-ℤ (inl (succ-ℕ n)) l =
  ( ap (add-ℤ (neg-ℤ l)) (commutative-mul-ℤ (inl n) l)) ∙
  ( inv (right-predecessor-law-mul-ℤ l (inl n)))
commutative-mul-ℤ (inr (inl star)) l = inv (right-zero-law-mul-ℤ l)
commutative-mul-ℤ (inr (inr zero-ℕ)) l = inv (right-unit-law-mul-ℤ l)
commutative-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( ap (add-ℤ l) (commutative-mul-ℤ (inr (inr n)) l)) ∙
  ( inv (right-successor-law-mul-ℤ l (in-pos n)))

left-distributive-mul-add-ℤ :
  (m k l : ℤ) → Id (mul-ℤ m (add-ℤ k l)) (add-ℤ (mul-ℤ m k) (mul-ℤ m l))
left-distributive-mul-add-ℤ m k l =
  commutative-mul-ℤ m (add-ℤ k l) ∙
    ( ( right-distributive-mul-add-ℤ k l m) ∙
      ( ap-add-ℤ (commutative-mul-ℤ k m) (commutative-mul-ℤ l m)))

right-negative-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ k (neg-ℤ l)) (neg-ℤ (mul-ℤ k l))
right-negative-law-mul-ℤ k l =
  ( ( commutative-mul-ℤ k (neg-ℤ l)) ∙
    ( left-negative-law-mul-ℤ l k)) ∙
  ( ap neg-ℤ (commutative-mul-ℤ l k))

interchange-law-mul-mul-ℤ : interchange-law mul-ℤ mul-ℤ
interchange-law-mul-mul-ℤ =
  interchange-law-commutative-and-associative
    mul-ℤ
    commutative-mul-ℤ
    associative-mul-ℤ

is-mul-neg-one-neg-ℤ : (x : ℤ) → Id (neg-ℤ x) (mul-ℤ neg-one-ℤ x)
is-mul-neg-one-neg-ℤ x = refl

is-mul-neg-one-neg-ℤ' : (x : ℤ) → Id (neg-ℤ x) (mul-ℤ x neg-one-ℤ)
is-mul-neg-one-neg-ℤ' x =
  is-mul-neg-one-neg-ℤ x ∙ commutative-mul-ℤ neg-one-ℤ x

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

## Negative and positive integers

```
is-nonnegative-ℤ : ℤ → UU lzero
is-nonnegative-ℤ (inl x) = empty
is-nonnegative-ℤ (inr k) = unit

is-nonnegative-eq-ℤ :
  {x y : ℤ} → Id x y → is-nonnegative-ℤ x → is-nonnegative-ℤ y
is-nonnegative-eq-ℤ refl = id

is-zero-is-nonnegative-ℤ :
  {x : ℤ} → is-nonnegative-ℤ x → is-nonnegative-ℤ (neg-ℤ x) → is-zero-ℤ x
is-zero-is-nonnegative-ℤ {inr (inl star)} H K = refl

is-nonnegative-succ-ℤ :
  (k : ℤ) → is-nonnegative-ℤ k → is-nonnegative-ℤ (succ-ℤ k)
is-nonnegative-succ-ℤ (inr (inl star)) p = star
is-nonnegative-succ-ℤ (inr (inr x)) p = star

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

-- We introduce positive integers

is-positive-ℤ : ℤ → UU lzero
is-positive-ℤ (inl x) = empty
is-positive-ℤ (inr (inl x)) = empty
is-positive-ℤ (inr (inr x)) = unit

positive-ℤ : UU lzero
positive-ℤ = Σ ℤ is-positive-ℤ

is-nonnegative-is-positive-ℤ : {x : ℤ} → is-positive-ℤ x → is-nonnegative-ℤ x
is-nonnegative-is-positive-ℤ {inr (inr x)} H = H

is-nonzero-is-positive-ℤ : (x : ℤ) → is-positive-ℤ x → is-nonzero-ℤ x
is-nonzero-is-positive-ℤ (inr (inr x)) H p = Eq-eq-ℤ p

is-positive-eq-ℤ : {x y : ℤ} → Id x y → is-positive-ℤ x → is-positive-ℤ y
is-positive-eq-ℤ {x} refl = id

is-positive-one-ℤ : is-positive-ℤ one-ℤ
is-positive-one-ℤ = star

one-positive-ℤ : positive-ℤ
pr1 one-positive-ℤ = one-ℤ
pr2 one-positive-ℤ = is-positive-one-ℤ

is-positive-succ-ℤ : {x : ℤ} → is-nonnegative-ℤ x → is-positive-ℤ (succ-ℤ x)
is-positive-succ-ℤ {inr (inl star)} H = is-positive-one-ℤ
is-positive-succ-ℤ {inr (inr x)} H = star

is-positive-add-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (add-ℤ x y)
is-positive-add-ℤ {inr (inr zero-ℕ)} {inr (inr y)} H K = star
is-positive-add-ℤ {inr (inr (succ-ℕ x))} {inr (inr y)} H K =
  is-positive-succ-ℤ
    ( is-nonnegative-is-positive-ℤ
      ( is-positive-add-ℤ {inr (inr x)} {inr (inr y)} star star))

is-positive-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (mul-ℤ x y)
is-positive-mul-ℤ {inr (inr zero-ℕ)} {inr (inr y)} H K = star
is-positive-mul-ℤ {inr (inr (succ-ℕ x))} {inr (inr y)} H K =
  is-positive-add-ℤ {inr (inr y)} K
    ( is-positive-mul-ℤ {inr (inr x)} {inr (inr y)} H K)

is-positive-int-ℕ :
  (x : ℕ) → is-nonzero-ℕ x → is-positive-ℤ (int-ℕ x)
is-positive-int-ℕ zero-ℕ H = ex-falso (H refl)
is-positive-int-ℕ (succ-ℕ x) H = star

-- Basics of nonnegative integers

nonnegative-ℤ : UU lzero
nonnegative-ℤ = Σ ℤ is-nonnegative-ℤ

int-nonnegative-ℤ : nonnegative-ℤ → ℤ
int-nonnegative-ℤ = pr1

is-nonnegative-int-nonnegative-ℤ :
  (x : nonnegative-ℤ) → is-nonnegative-ℤ (int-nonnegative-ℤ x)
is-nonnegative-int-nonnegative-ℤ = pr2

is-injective-int-nonnegative-ℤ : is-injective int-nonnegative-ℤ
is-injective-int-nonnegative-ℤ {pair (inr x) star} {pair (inr .x) star} refl =
  refl

is-nonnegative-int-ℕ : (n : ℕ) → is-nonnegative-ℤ (int-ℕ n)
is-nonnegative-int-ℕ zero-ℕ = star
is-nonnegative-int-ℕ (succ-ℕ n) = star

nonnegative-int-ℕ : ℕ → nonnegative-ℤ
pr1 (nonnegative-int-ℕ n) = int-ℕ n
pr2 (nonnegative-int-ℕ n) = is-nonnegative-int-ℕ n

nat-nonnegative-ℤ : nonnegative-ℤ → ℕ
nat-nonnegative-ℤ (pair (inr (inl x)) H) = zero-ℕ
nat-nonnegative-ℤ (pair (inr (inr x)) H) = succ-ℕ x

issec-nat-nonnegative-ℤ :
  (x : nonnegative-ℤ) → Id (nonnegative-int-ℕ (nat-nonnegative-ℤ x)) x
issec-nat-nonnegative-ℤ (pair (inr (inl star)) star) = refl
issec-nat-nonnegative-ℤ (pair (inr (inr x)) star) = refl

isretr-nat-nonnegative-ℤ :
  (n : ℕ) → Id (nat-nonnegative-ℤ (nonnegative-int-ℕ n)) n
isretr-nat-nonnegative-ℤ zero-ℕ = refl
isretr-nat-nonnegative-ℤ (succ-ℕ n) = refl

is-injective-nonnegative-int-ℕ : is-injective nonnegative-int-ℕ
is-injective-nonnegative-int-ℕ {x} {y} p =
  ( inv (isretr-nat-nonnegative-ℤ x)) ∙
  ( ( ap nat-nonnegative-ℤ p) ∙
    ( isretr-nat-nonnegative-ℤ y))

decide-is-nonnegative-ℤ :
  {x : ℤ} → coprod (is-nonnegative-ℤ x) (is-nonnegative-ℤ (neg-ℤ x))
decide-is-nonnegative-ℤ {inl x} = inr star
decide-is-nonnegative-ℤ {inr x} = inl star
```
