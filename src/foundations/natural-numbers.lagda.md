---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.natural-numbers where

open import foundations.functions using (_∘_)
open import foundations.identity-types using (Id; refl; _∙_; inv; ap; ap-binary)
open import foundations.laws-for-operations using
  ( interchange-law; interchange-law-commutative-and-associative)
open import foundations.levels using (Level; lzero; UU)
```

# The type of natural numbers

```agda
data ℕ : UU lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
```

## The induction principle of ℕ

```agda
ind-ℕ :
  {i : Level} {P : ℕ → UU i} →
  P 0 → ((n : ℕ) → P n → P(succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ p0 pS 0 = p0
ind-ℕ p0 pS (succ-ℕ n) = pS n (ind-ℕ p0 pS n)
```

##  Addition and multiplication on ℕ

```agda
add-ℕ : ℕ → ℕ → ℕ
add-ℕ x 0 = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)

add-ℕ' : ℕ → ℕ → ℕ
add-ℕ' m n = add-ℕ n m

ap-add-ℕ :
  {m n m' n' : ℕ} → Id m m' → Id n n' → Id (add-ℕ m n) (add-ℕ m' n')
ap-add-ℕ p q = ap-binary add-ℕ p q

mul-ℕ : ℕ → (ℕ → ℕ)
mul-ℕ 0 n = 0
mul-ℕ (succ-ℕ m) n = add-ℕ (mul-ℕ m n) n

mul-ℕ' : ℕ → (ℕ → ℕ)
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
```

## The triangular numbers

```agda
triangular-number-ℕ : ℕ → ℕ
triangular-number-ℕ 0 = 0
triangular-number-ℕ (succ-ℕ n) = add-ℕ (triangular-number-ℕ n) (succ-ℕ n)
```

## Factorials

```agda
factorial-ℕ : ℕ → ℕ
factorial-ℕ 0 = 1
factorial-ℕ (succ-ℕ m) = mul-ℕ (factorial-ℕ m) (succ-ℕ m)
```

## Binomial coefficients

```agda
_choose-ℕ_ : ℕ → ℕ → ℕ
0 choose-ℕ 0 = 1
0 choose-ℕ succ-ℕ k = 0
(succ-ℕ n) choose-ℕ 0 = 1
(succ-ℕ n) choose-ℕ (succ-ℕ k) = add-ℕ (n choose-ℕ k) (n choose-ℕ (succ-ℕ k))
```

## The Fibonacci sequence

```agda
Fibonacci-ℕ : ℕ → ℕ
Fibonacci-ℕ 0 = 0
Fibonacci-ℕ (succ-ℕ 0) = 1
Fibonacci-ℕ (succ-ℕ (succ-ℕ n)) = add-ℕ (Fibonacci-ℕ (succ-ℕ n)) (Fibonacci-ℕ n)
```

The above definition of the Fibonacci sequence uses Agda's rather strong
pattern matching definitions. Below, we will give a definition of the
Fibonacci sequence in terms of `ind-ℕ`.

The problem with defining the Fibonacci sequence using `ind-ℕ`, is that `ind-ℕ`
doesn't give us a way to refer to both `(F n)` and `(F (succ-ℕ n))`. So, we have
to give a workaround, where we store two values in the Fibonacci sequence
at once.

The basic idea is that we define a sequence of pairs of integers, which will
be consecutive Fibonacci numbers. This would be a function of type $ℕ → ℕ²$.

Such a function is easy to give with induction, using the map $ℕ² → ℕ²$ that
takes a pair `(m,n)` to the pair `(n,n+m)`. Starting the iteration with `(0,1)`
we obtain the Fibonacci sequence by taking the first projection.

However, we haven't defined cartesian products or booleans yet. Therefore
we mimic the above idea, using $ℕ → ℕ$ instead of $ℕ²$.

```agda
shift-one : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-one n f = ind-ℕ n (λ x y → f x)

shift-two : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-two m n f = shift-one m (shift-one n f)

Fibo-zero-ℕ : ℕ → ℕ
Fibo-zero-ℕ = shift-two 0 1 (λ x → 0)

Fibo-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
Fibo-succ-ℕ f = shift-two (f 1) (add-ℕ (f 1) (f 0)) (λ x → 0)

Fibo-function : ℕ → ℕ → ℕ
Fibo-function =
  ind-ℕ
    ( Fibo-zero-ℕ)
    ( λ n → Fibo-succ-ℕ)

Fibo : ℕ → ℕ
Fibo k = Fibo-function k 0
```

## Division by two rounded down

We first define division by two by pattern matching. Then we provide an alternative definition using the induction principle of ℕ.

```agda
div-two-ℕ : ℕ → ℕ
div-two-ℕ 0 = 0
div-two-ℕ (succ-ℕ 0) = 0
div-two-ℕ (succ-ℕ (succ-ℕ n)) = succ-ℕ (div-two-ℕ n)

div-two-zero-ℕ : ℕ → ℕ
div-two-zero-ℕ x = 0

div-two-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
div-two-succ-ℕ f = shift-two (f 1) (succ-ℕ (f 0)) (λ x → 0)

div-two-function : ℕ → ℕ → ℕ
div-two-function = ind-ℕ div-two-zero-ℕ (λ n → div-two-succ-ℕ)

div-two-ℕ' : ℕ → ℕ
div-two-ℕ' n = div-two-function n 0
```

## The laws of addition on ℕ

```agda
right-unit-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ x zero-ℕ) x
right-unit-law-add-ℕ x = refl

left-unit-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ zero-ℕ x) x
left-unit-law-add-ℕ zero-ℕ = refl
left-unit-law-add-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-add-ℕ x)

left-successor-law-add-ℕ :
  (x y : ℕ) → Id (add-ℕ (succ-ℕ x) y) (succ-ℕ (add-ℕ x y))
left-successor-law-add-ℕ x zero-ℕ = refl
left-successor-law-add-ℕ x (succ-ℕ y) =
  ap succ-ℕ (left-successor-law-add-ℕ x y)
                                        
right-successor-law-add-ℕ :
  (x y : ℕ) → Id (add-ℕ x (succ-ℕ y)) (succ-ℕ (add-ℕ x y))
right-successor-law-add-ℕ x y = refl

associative-add-ℕ :
  (x y z : ℕ) → Id (add-ℕ (add-ℕ x y) z) (add-ℕ x (add-ℕ y z))
associative-add-ℕ x y zero-ℕ = refl 
associative-add-ℕ x y (succ-ℕ z) = ap succ-ℕ (associative-add-ℕ x y z)

commutative-add-ℕ : (x y : ℕ) → Id (add-ℕ x y) (add-ℕ y x)
commutative-add-ℕ zero-ℕ y = left-unit-law-add-ℕ y
commutative-add-ℕ (succ-ℕ x) y =
  (left-successor-law-add-ℕ x y) ∙ (ap succ-ℕ (commutative-add-ℕ x y))

left-one-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ 1 x) (succ-ℕ x)
left-one-law-add-ℕ x =
  ( left-successor-law-add-ℕ zero-ℕ x) ∙
  ( ap succ-ℕ (left-unit-law-add-ℕ x))

right-one-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ x 1) (succ-ℕ x)
right-one-law-add-ℕ x = refl

left-two-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ 2 x) (succ-ℕ (succ-ℕ x))
left-two-law-add-ℕ x =
  ( left-successor-law-add-ℕ 1 x) ∙
  ( ap succ-ℕ (left-one-law-add-ℕ x))

right-two-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ x 2) (succ-ℕ (succ-ℕ x))
right-two-law-add-ℕ x = refl

interchange-law-add-add-ℕ : interchange-law add-ℕ add-ℕ
interchange-law-add-add-ℕ =
  interchange-law-commutative-and-associative
    add-ℕ
    commutative-add-ℕ
    associative-add-ℕ
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
```

## Compute division by two rounded down

```agda
comp-even-div-two-ℕ :
  (n : ℕ) → Id (div-two-ℕ (mul-ℕ 2 n)) n
comp-even-div-two-ℕ zero-ℕ = refl
comp-even-div-two-ℕ (succ-ℕ n) =
  ( ap div-two-ℕ (right-successor-law-mul-ℕ 2 n)) ∙
  ( ( ap div-two-ℕ (left-two-law-add-ℕ (mul-ℕ 2 n))) ∙
    ( ap succ-ℕ (comp-even-div-two-ℕ n)))

comp-odd-div-two-ℕ :
  (n : ℕ) → Id (div-two-ℕ (succ-ℕ (mul-ℕ 2 n))) n
comp-odd-div-two-ℕ zero-ℕ = refl
comp-odd-div-two-ℕ (succ-ℕ n) =
   ( ap ( div-two-ℕ ∘ succ-ℕ)
        ( ( right-successor-law-mul-ℕ 2 n) ∙
          ( left-two-law-add-ℕ (mul-ℕ 2 n)))) ∙
   ( ap succ-ℕ (comp-odd-div-two-ℕ n))
```
