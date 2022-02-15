---
title: Univalent Mathematics in Agda
---

# Multiplication of natural numbers

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.multiplication-natural-numbers where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; add-ℕ'; right-unit-law-add-ℕ; associative-add-ℕ;
    left-successor-law-add-ℕ; commutative-add-ℕ; is-injective-add-ℕ';
    is-zero-right-is-zero-add-ℕ; neq-add-ℕ)
open import elementary-number-theory.equality-natural-numbers using (is-set-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-one-ℕ; is-nonzero-ℕ; is-successor-is-nonzero-ℕ;
    is-injective-succ-ℕ)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.empty-types using (ex-falso)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap; ap-binary)
open import foundation.injective-maps using (is-injective; is-emb-is-injective)
open import foundation.interchange-law using
  ( interchange-law; interchange-law-commutative-and-associative)
open import foundation.negation using (¬)
```

# Multiplication on the natural numbers

```agda
mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ 0 n = 0
mul-ℕ (succ-ℕ m) n = add-ℕ (mul-ℕ m n) n

mul-ℕ' : ℕ → ℕ → ℕ
mul-ℕ' x y = mul-ℕ y x

ap-mul-ℕ :
  {x y x' y' : ℕ} → Id x x' → Id y y' → Id (mul-ℕ x y) (mul-ℕ x' y')
ap-mul-ℕ p q = ap-binary mul-ℕ p q

exp-ℕ : ℕ → (ℕ → ℕ)
exp-ℕ m 0 = 1
exp-ℕ m (succ-ℕ n) = mul-ℕ (exp-ℕ m n) m

double-ℕ : ℕ → ℕ
double-ℕ x = mul-ℕ 2 x

triple-ℕ : ℕ → ℕ
triple-ℕ x = mul-ℕ 3 x

square-ℕ : ℕ → ℕ
square-ℕ x = mul-ℕ x x

cube-ℕ : ℕ → ℕ
cube-ℕ x = mul-ℕ (square-ℕ x) x
```

## Laws for multiplication on ℕ

```agda
abstract
  left-zero-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ zero-ℕ x) zero-ℕ
  left-zero-law-mul-ℕ x = refl

  right-zero-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ x zero-ℕ) zero-ℕ
  right-zero-law-mul-ℕ zero-ℕ = refl
  right-zero-law-mul-ℕ (succ-ℕ x) =
    ( right-unit-law-add-ℕ (mul-ℕ x zero-ℕ)) ∙ (right-zero-law-mul-ℕ x)

abstract
  right-unit-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ x 1) x
  right-unit-law-mul-ℕ zero-ℕ = refl
  right-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (right-unit-law-mul-ℕ x)

  left-unit-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ 1 x) x
  left-unit-law-mul-ℕ zero-ℕ = refl
  left-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-mul-ℕ x)

abstract
  left-successor-law-mul-ℕ :
    (x y : ℕ) → Id (mul-ℕ (succ-ℕ x) y) (add-ℕ (mul-ℕ x y) y)
  left-successor-law-mul-ℕ x y = refl

  right-successor-law-mul-ℕ :
    (x y : ℕ) → Id (mul-ℕ x (succ-ℕ y)) (add-ℕ x (mul-ℕ x y))
  right-successor-law-mul-ℕ zero-ℕ y = refl
  right-successor-law-mul-ℕ (succ-ℕ x) y =
    ( ( ap (λ t → succ-ℕ (add-ℕ t y)) (right-successor-law-mul-ℕ x y)) ∙
      ( ap succ-ℕ (associative-add-ℕ x (mul-ℕ x y) y))) ∙
    ( inv (left-successor-law-add-ℕ x (add-ℕ (mul-ℕ x y) y)))

square-succ-ℕ :
  (k : ℕ) →
  Id (square-ℕ (succ-ℕ k)) (succ-ℕ (mul-ℕ (succ-ℕ (succ-ℕ k)) k))
square-succ-ℕ k =
  ( right-successor-law-mul-ℕ (succ-ℕ k) k) ∙
  ( commutative-add-ℕ (succ-ℕ k) (mul-ℕ (succ-ℕ k) k))

abstract
  commutative-mul-ℕ :
    (x y : ℕ) → Id (mul-ℕ x y) (mul-ℕ y x)
  commutative-mul-ℕ zero-ℕ y = inv (right-zero-law-mul-ℕ y)
  commutative-mul-ℕ (succ-ℕ x) y =
    ( commutative-add-ℕ (mul-ℕ x y) y) ∙ 
    ( ( ap (add-ℕ y) (commutative-mul-ℕ x y)) ∙
      ( inv (right-successor-law-mul-ℕ y x)))

abstract
  left-distributive-mul-add-ℕ :
    (x y z : ℕ) → Id (mul-ℕ x (add-ℕ y z)) (add-ℕ (mul-ℕ x y) (mul-ℕ x z))
  left-distributive-mul-add-ℕ zero-ℕ y z = refl
  left-distributive-mul-add-ℕ (succ-ℕ x) y z =
    ( left-successor-law-mul-ℕ x (add-ℕ y z)) ∙ 
    ( ( ap (add-ℕ' (add-ℕ y z)) (left-distributive-mul-add-ℕ x y z)) ∙ 
      ( ( associative-add-ℕ (mul-ℕ x y) (mul-ℕ x z) (add-ℕ y z)) ∙
        ( ( ap ( add-ℕ (mul-ℕ x y)) 
               ( ( inv (associative-add-ℕ (mul-ℕ x z) y z)) ∙
                 ( ( ap (add-ℕ' z) (commutative-add-ℕ (mul-ℕ x z) y)) ∙
                   ( associative-add-ℕ y (mul-ℕ x z) z)))) ∙ 
          ( inv (associative-add-ℕ (mul-ℕ x y) y (add-ℕ (mul-ℕ x z) z))))))

abstract
  right-distributive-mul-add-ℕ :
    (x y z : ℕ) → Id (mul-ℕ (add-ℕ x y) z) (add-ℕ (mul-ℕ x z) (mul-ℕ y z))
  right-distributive-mul-add-ℕ x y z =
    ( commutative-mul-ℕ (add-ℕ x y) z) ∙ 
    ( ( left-distributive-mul-add-ℕ z x y) ∙ 
      ( ( ap (add-ℕ' (mul-ℕ z y)) (commutative-mul-ℕ z x)) ∙ 
        ( ap (add-ℕ (mul-ℕ x z)) (commutative-mul-ℕ z y))))

abstract
  associative-mul-ℕ :
    (x y z : ℕ) → Id (mul-ℕ (mul-ℕ x y) z) (mul-ℕ x (mul-ℕ y z))
  associative-mul-ℕ zero-ℕ y z = refl
  associative-mul-ℕ (succ-ℕ x) y z =
    ( right-distributive-mul-add-ℕ (mul-ℕ x y) y z) ∙ 
    ( ap (add-ℕ' (mul-ℕ y z)) (associative-mul-ℕ x y z))

left-two-law-mul-ℕ :
  (x : ℕ) → Id (mul-ℕ 2 x) (add-ℕ x x)
left-two-law-mul-ℕ x =
  ( left-successor-law-mul-ℕ 1 x) ∙
  ( ap (add-ℕ' x) (left-unit-law-mul-ℕ x))

right-two-law-mul-ℕ :
  (x : ℕ) → Id (mul-ℕ x 2) (add-ℕ x x)
right-two-law-mul-ℕ x =
  ( right-successor-law-mul-ℕ x 1) ∙
  ( ap (add-ℕ x) (right-unit-law-mul-ℕ x))

interchange-law-mul-mul-ℕ : interchange-law mul-ℕ mul-ℕ
interchange-law-mul-mul-ℕ =
  interchange-law-commutative-and-associative
    mul-ℕ
    commutative-mul-ℕ
    associative-mul-ℕ

is-injective-mul-succ-ℕ' :
  (k : ℕ) → is-injective (mul-ℕ' (succ-ℕ k))
is-injective-mul-succ-ℕ' k {zero-ℕ} {zero-ℕ} p = refl
is-injective-mul-succ-ℕ' k {succ-ℕ m} {succ-ℕ n} p =
  ap succ-ℕ
    ( is-injective-mul-succ-ℕ' k {m} {n}
      ( is-injective-add-ℕ'
        ( succ-ℕ k)
        ( ( inv (left-successor-law-mul-ℕ m (succ-ℕ k))) ∙
          ( ( p) ∙
            ( left-successor-law-mul-ℕ n (succ-ℕ k))))))

is-injective-mul-ℕ' :
  (k : ℕ) → is-nonzero-ℕ k → is-injective (mul-ℕ' k)
is-injective-mul-ℕ' k H p with
  is-successor-is-nonzero-ℕ H
... | pair l refl = is-injective-mul-succ-ℕ' l p

is-injective-mul-succ-ℕ :
  (k : ℕ) → is-injective (mul-ℕ (succ-ℕ k))
is-injective-mul-succ-ℕ k {m} {n} p =
  is-injective-mul-succ-ℕ' k
    ( ( commutative-mul-ℕ m (succ-ℕ k)) ∙
      ( p ∙ commutative-mul-ℕ (succ-ℕ k) n))

is-injective-mul-ℕ :
  (k : ℕ) → is-nonzero-ℕ k → is-injective (mul-ℕ k)
is-injective-mul-ℕ k H p with
  is-successor-is-nonzero-ℕ H
... | pair l refl = is-injective-mul-succ-ℕ l p

is-emb-mul-ℕ : (x : ℕ) → is-nonzero-ℕ x → is-emb (mul-ℕ x)
is-emb-mul-ℕ x H = is-emb-is-injective is-set-ℕ (is-injective-mul-ℕ x H)

is-emb-mul-ℕ' : (x : ℕ) → is-nonzero-ℕ x → is-emb (mul-ℕ' x)
is-emb-mul-ℕ' x H = is-emb-is-injective is-set-ℕ (is-injective-mul-ℕ' x H)

is-nonzero-mul-ℕ :
  (x y : ℕ) → is-nonzero-ℕ x → is-nonzero-ℕ y → is-nonzero-ℕ (mul-ℕ x y)
is-nonzero-mul-ℕ x y H K p =
  K (is-injective-mul-ℕ x H (p ∙ (inv (right-zero-law-mul-ℕ x))))

-- We conclude that y = 1 if (x+1)y = x+1

is-one-is-right-unit-mul-ℕ :
  (x y : ℕ) → Id (mul-ℕ (succ-ℕ x) y) (succ-ℕ x) → is-one-ℕ y
is-one-is-right-unit-mul-ℕ x y p =
  is-injective-mul-succ-ℕ x (p ∙ inv (right-unit-law-mul-ℕ (succ-ℕ x)))

is-one-is-left-unit-mul-ℕ :
  (x y : ℕ) → Id (mul-ℕ x (succ-ℕ y)) (succ-ℕ y) → is-one-ℕ x
is-one-is-left-unit-mul-ℕ x y p =
  is-injective-mul-succ-ℕ' y (p ∙ inv (left-unit-law-mul-ℕ (succ-ℕ y)))

is-one-right-is-one-mul-ℕ :
  (x y : ℕ) → is-one-ℕ (mul-ℕ x y) → is-one-ℕ y
is-one-right-is-one-mul-ℕ zero-ℕ zero-ℕ p = p
is-one-right-is-one-mul-ℕ zero-ℕ (succ-ℕ y) ()
is-one-right-is-one-mul-ℕ (succ-ℕ x) zero-ℕ p =
  is-one-right-is-one-mul-ℕ x zero-ℕ p
is-one-right-is-one-mul-ℕ (succ-ℕ x) (succ-ℕ y) p = 
  ap ( succ-ℕ)
     ( is-zero-right-is-zero-add-ℕ (mul-ℕ x (succ-ℕ y)) y
       ( is-injective-succ-ℕ p))
       
is-one-left-is-one-mul-ℕ :
  (x y : ℕ) → is-one-ℕ (mul-ℕ x y) → is-one-ℕ x
is-one-left-is-one-mul-ℕ x y p =
  is-one-right-is-one-mul-ℕ y x (commutative-mul-ℕ y x ∙ p)

neq-mul-ℕ :
  (m n : ℕ) → ¬ (Id (succ-ℕ m) (mul-ℕ (succ-ℕ m) (succ-ℕ (succ-ℕ n))))
neq-mul-ℕ m n p =
  neq-add-ℕ
    ( succ-ℕ m)
    ( add-ℕ (mul-ℕ m (succ-ℕ n)) n)
    ( ( p) ∙
      ( ( right-successor-law-mul-ℕ (succ-ℕ m) (succ-ℕ n)) ∙
        ( ap (add-ℕ (succ-ℕ m)) (left-successor-law-mul-ℕ m (succ-ℕ n)))))

annihilation-law-exp-ℕ : (n : ℕ) → Id (exp-ℕ 1 n) 1
annihilation-law-exp-ℕ zero-ℕ = refl
annihilation-law-exp-ℕ (succ-ℕ n) = right-unit-law-mul-ℕ (exp-ℕ 1 n) ∙ annihilation-law-exp-ℕ n

left-distributive-exp-add-ℕ : (x y z : ℕ) → Id (exp-ℕ x (add-ℕ y z)) (mul-ℕ (exp-ℕ x y) (exp-ℕ x z))
left-distributive-exp-add-ℕ x y zero-ℕ = inv (right-unit-law-mul-ℕ (exp-ℕ x y))
left-distributive-exp-add-ℕ x y (succ-ℕ z) =
  ( ap (mul-ℕ' x) (left-distributive-exp-add-ℕ x y z) ) ∙
  ( associative-mul-ℕ (exp-ℕ x y) (exp-ℕ x z) x )

right-distributive-exp-mul-ℕ : (x y z : ℕ) → Id (exp-ℕ (mul-ℕ x y) z) (mul-ℕ (exp-ℕ x z) (exp-ℕ y z))
right-distributive-exp-mul-ℕ x y zero-ℕ = refl
right-distributive-exp-mul-ℕ x y (succ-ℕ z) =
  ( ap (mul-ℕ' (mul-ℕ x y)) (right-distributive-exp-mul-ℕ x y z) ) ∙
  ( interchange-law-mul-mul-ℕ (exp-ℕ x z) (exp-ℕ y z) x y )

exp-mul-ℕ : (x y z : ℕ) → Id (exp-ℕ (exp-ℕ x y) z) (exp-ℕ x (mul-ℕ y z))
exp-mul-ℕ x zero-ℕ z = annihilation-law-exp-ℕ z
exp-mul-ℕ x (succ-ℕ y) z =
  ( right-distributive-exp-mul-ℕ (exp-ℕ x y) x z) ∙
  ( (ap (mul-ℕ' (exp-ℕ x z)) (exp-mul-ℕ x y z) ) ∙
    (inv (left-distributive-exp-add-ℕ x (mul-ℕ y z) z)))
```
