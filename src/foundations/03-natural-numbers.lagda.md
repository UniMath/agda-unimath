---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.03-natural-numbers where

open import foundations.02-pi public
```


## The formal specification of the type of natural numbers

```agda
data ℕ : UU lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
```

Example of some natural numbers:

```agda
one-ℕ : ℕ
one-ℕ = 1

two-ℕ : ℕ
two-ℕ = 2
```

```agda
ind-ℕ : {i : Level} {P : ℕ → UU i}
  → P zero-ℕ
  → ((n : ℕ) → P n → P(succ-ℕ n))
  → ((n : ℕ) → P n)
ind-ℕ p0 pS zero-ℕ = p0
ind-ℕ p0 pS (succ-ℕ n) = pS n (ind-ℕ p0 pS n)
```

##  Examples of functions on the natural numbers

```agda
add-ℕ : ℕ → ℕ → ℕ
add-ℕ x zero-ℕ = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)
```

```agda
add-ℕ' : ℕ → ℕ → ℕ
add-ℕ' m n = add-ℕ n m
```

```agda
mul-ℕ : ℕ → (ℕ → ℕ)
mul-ℕ zero-ℕ n = zero-ℕ
mul-ℕ (succ-ℕ m) n = add-ℕ (mul-ℕ m n) n

mul-ℕ' : ℕ → (ℕ → ℕ)
mul-ℕ' x y = mul-ℕ y x
```

```agda
exp-ℕ : ℕ → (ℕ → ℕ)
exp-ℕ m zero-ℕ = one-ℕ
exp-ℕ m (succ-ℕ n) = mul-ℕ (exp-ℕ m n) m
```

```agda
double-ℕ : ℕ → ℕ
double-ℕ x = mul-ℕ two-ℕ x
```

```agda
triple-ℕ : ℕ → ℕ
triple-ℕ x = mul-ℕ 3 x
```

```agda
square-ℕ : ℕ → ℕ
square-ℕ x = mul-ℕ x x
```

```agda
cube-ℕ : ℕ → ℕ
cube-ℕ x = mul-ℕ (square-ℕ x) x
```

```agda
min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ zero-ℕ n = zero-ℕ
min-ℕ (succ-ℕ m) zero-ℕ = zero-ℕ
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)
```

```agda
max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ zero-ℕ n = n
max-ℕ (succ-ℕ m) zero-ℕ = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)
```

```agda
triangular-number-ℕ : ℕ → ℕ
triangular-number-ℕ zero-ℕ = zero-ℕ
triangular-number-ℕ (succ-ℕ n) = add-ℕ (triangular-number-ℕ n) (succ-ℕ n)
```

```agda
factorial-ℕ : ℕ → ℕ
factorial-ℕ zero-ℕ = one-ℕ
factorial-ℕ (succ-ℕ m) = mul-ℕ (factorial-ℕ m) (succ-ℕ m)
```

```agda
_choose-ℕ_ : ℕ → ℕ → ℕ
zero-ℕ choose-ℕ zero-ℕ = one-ℕ
zero-ℕ choose-ℕ succ-ℕ k = zero-ℕ
(succ-ℕ n) choose-ℕ zero-ℕ = one-ℕ
(succ-ℕ n) choose-ℕ (succ-ℕ k) = add-ℕ (n choose-ℕ k) (n choose-ℕ (succ-ℕ k))
```

## The Fibonacci sequence

```agda
Fibonacci-ℕ : ℕ → ℕ
Fibonacci-ℕ zero-ℕ = zero-ℕ
Fibonacci-ℕ (succ-ℕ zero-ℕ) = one-ℕ
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
```

```agda
shift-two : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-two m n f = shift-one m (shift-one n f)
```

```agda
Fibo-zero-ℕ : ℕ → ℕ
Fibo-zero-ℕ = shift-two zero-ℕ one-ℕ (const ℕ ℕ zero-ℕ)
```

```agda
Fibo-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
Fibo-succ-ℕ f =
  shift-two (f one-ℕ) (add-ℕ (f one-ℕ) (f zero-ℕ)) (const ℕ ℕ zero-ℕ)
```

```agda
Fibo-function : ℕ → ℕ → ℕ
Fibo-function =
  ind-ℕ
    ( Fibo-zero-ℕ)
    ( λ n → Fibo-succ-ℕ)
```

```agda
Fibo : ℕ → ℕ
Fibo k = Fibo-function k zero-ℕ
```

## Division

```agda
div-two-ℕ : ℕ → ℕ
div-two-ℕ zero-ℕ = zero-ℕ
div-two-ℕ (succ-ℕ zero-ℕ) = zero-ℕ
div-two-ℕ (succ-ℕ (succ-ℕ n)) = succ-ℕ (div-two-ℕ n)
```

```agda
div-two-zero-ℕ : ℕ → ℕ
div-two-zero-ℕ = const ℕ ℕ zero-ℕ
```

```agda
div-two-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
div-two-succ-ℕ f =
  shift-two (f one-ℕ) (succ-ℕ (f zero-ℕ)) (const ℕ ℕ zero-ℕ)
```

```agda
div-two-function : ℕ → ℕ → ℕ
div-two-function = ind-ℕ div-two-zero-ℕ (λ n → div-two-succ-ℕ)
```

```agda
div-two-ℕ' : ℕ → ℕ
div-two-ℕ' n = div-two-function n zero-ℕ
```
