---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.multiplication-integers where

open import foundations.addition-integers using
  ( add-ℤ; add-ℤ'; ap-add-ℤ; right-inverse-law-add-ℤ; left-unit-law-add-ℤ;
    associative-add-ℤ; right-unit-law-add-ℤ; left-inverse-law-add-ℤ;
    right-successor-law-add-ℤ; commutative-add-ℤ; left-successor-law-add-ℤ;
    left-predecessor-law-add-ℤ; right-negative-law-add-ℤ;
    distributive-neg-add-ℤ; is-positive-add-ℤ)
open import foundations.identity-types using (Id; refl; _∙_; inv; ap; ap-binary)
open import foundations.integers using
  ( ℤ; inl; inr; neg-ℤ; zero-ℤ; one-ℤ; neg-one-ℤ; int-ℕ; succ-ℤ; pred-ℤ;
    in-pos; pred-neg-ℤ; issec-pred-ℤ; neg-pred-ℤ; neg-neg-ℤ; is-positive-ℤ)
open import foundations.laws-for-operations using
  ( interchange-law; interchange-law-commutative-and-associative)
open import foundations.multiplication-natural-numbers using
  (mul-ℕ)
open import foundations.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import foundations.unit-type using (star)
```

# Multiplication of integers

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
```

```agda
is-positive-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (mul-ℤ x y)
is-positive-mul-ℤ {inr (inr zero-ℕ)} {inr (inr y)} H K = star
is-positive-mul-ℤ {inr (inr (succ-ℕ x))} {inr (inr y)} H K =
  is-positive-add-ℤ {inr (inr y)} K
    ( is-positive-mul-ℤ {inr (inr x)} {inr (inr y)} H K)
```
