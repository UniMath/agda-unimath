---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.08-integers where

open import foundations.08-decidability-in-number-theory public

{-------------------------------------------------------------------------------

  The Integers
  ------------

  In this file we extend the constructions of the previous sections to the 
  integers.

-------------------------------------------------------------------------------}

-- We prove compatibility of the operations on ℤ and on ℕ

succ-int-ℕ : (x : ℕ) → Id (succ-ℤ (int-ℕ x)) (int-ℕ (succ-ℕ x))
succ-int-ℕ zero-ℕ = refl
succ-int-ℕ (succ-ℕ x) = refl

add-int-ℕ : (x y : ℕ) → Id (add-ℤ (int-ℕ x) (int-ℕ y)) (int-ℕ (add-ℕ x y))
add-int-ℕ x zero-ℕ = right-unit-law-add-ℤ (int-ℕ x)
add-int-ℕ x (succ-ℕ y) =
  ( ap (add-ℤ (int-ℕ x)) (inv (succ-int-ℕ y))) ∙
  ( ( right-successor-law-add-ℤ (int-ℕ x) (int-ℕ y)) ∙
    ( ( ap succ-ℤ (add-int-ℕ x y)) ∙
      ( succ-int-ℕ (add-ℕ x y))))

mul-int-ℕ : (x y : ℕ) → Id (mul-ℤ (int-ℕ x) (int-ℕ y)) (int-ℕ (mul-ℕ x y))
mul-int-ℕ zero-ℕ y = refl
mul-int-ℕ (succ-ℕ x) y =
  ( ap (mul-ℤ' (int-ℕ y)) (inv (succ-int-ℕ x))) ∙
  ( ( left-successor-law-mul-ℤ (int-ℕ x) (int-ℕ y)) ∙
    ( ( ( ap (add-ℤ (int-ℕ y)) (mul-int-ℕ x y)) ∙
        ( add-int-ℕ y (mul-ℕ x y))) ∙
      ( ap int-ℕ (commutative-add-ℕ y (mul-ℕ x y)))))

compute-mul-ℤ : (x y : ℤ) → Id (mul-ℤ x y) (explicit-mul-ℤ x y)
compute-mul-ℤ (inl zero-ℕ) (inl y) =
  inv (ap int-ℕ (left-unit-law-mul-ℕ (succ-ℕ y)))
compute-mul-ℤ (inl (succ-ℕ x)) (inl y) =
  ( ( ap (add-ℤ (int-ℕ (succ-ℕ y))) (compute-mul-ℤ (inl x) (inl y))) ∙
    ( commutative-add-ℤ
      ( int-ℕ (succ-ℕ y))
      ( int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y))))) ∙
  ( add-int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)) (succ-ℕ y))
compute-mul-ℤ (inl zero-ℕ) (inr (inl star)) = refl
compute-mul-ℤ (inl zero-ℕ) (inr (inr x)) = ap inl (inv (left-unit-law-add-ℕ x))
compute-mul-ℤ (inl (succ-ℕ x)) (inr (inl star)) = right-zero-law-mul-ℤ (inl x)
compute-mul-ℤ (inl (succ-ℕ x)) (inr (inr y)) =
  ( ( ( ap (add-ℤ (inl y)) (compute-mul-ℤ (inl x) (inr (inr y)))) ∙
      ( inv
        ( distributive-neg-add-ℤ
          ( inr (inr y))
          ( int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)))))) ∙
    ( ap
      ( neg-ℤ)
      ( commutative-add-ℤ
        ( int-ℕ (succ-ℕ y))
        ( int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)))))) ∙
  ( ap neg-ℤ (add-int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)) (succ-ℕ y)))
compute-mul-ℤ (inr (inl star)) (inl y) = refl
compute-mul-ℤ (inr (inr zero-ℕ)) (inl y) = ap inl (inv (left-unit-law-add-ℕ y))
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inl y) =
  ( ap (add-ℤ (inl y)) (compute-mul-ℤ (inr (inr x)) (inl y))) ∙
  ( ( ( inv
        ( distributive-neg-add-ℤ
          ( inr (inr y))
          ( inr (inr (add-ℕ (mul-ℕ x (succ-ℕ y)) y))))) ∙
      ( ap
        ( neg-ℤ)
        ( ( add-int-ℕ (succ-ℕ y) (mul-ℕ (succ-ℕ x) (succ-ℕ y))) ∙
          ( ap
            ( inr ∘ inr)
            ( left-successor-law-add-ℕ y (add-ℕ (mul-ℕ x (succ-ℕ y)) y)))))) ∙
    ( ap inl (commutative-add-ℕ y (mul-ℕ (succ-ℕ x) (succ-ℕ y)))))
compute-mul-ℤ (inr (inl star)) (inr (inl star)) = refl
compute-mul-ℤ (inr (inl star)) (inr (inr y)) = refl
compute-mul-ℤ (inr (inr zero-ℕ)) (inr (inl star)) = refl
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inl star)) =
  right-zero-law-mul-ℤ (inr (inr (succ-ℕ x)))
compute-mul-ℤ (inr (inr zero-ℕ)) (inr (inr y)) =
  ap ( inr ∘ inr)
     ( inv
       ( ( ap (add-ℕ' y) (left-zero-law-mul-ℕ (succ-ℕ y))) ∙
         ( left-unit-law-add-ℕ y)))
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inr y)) =
  ( ap (add-ℤ (inr (inr y))) (compute-mul-ℤ (inr (inr x)) (inr (inr y)))) ∙
  ( ( add-int-ℕ (succ-ℕ y) (mul-ℕ (succ-ℕ x) (succ-ℕ y))) ∙
    ( ap int-ℕ (commutative-add-ℕ (succ-ℕ y) (mul-ℕ (succ-ℕ x) (succ-ℕ y)))))

-- We show that mul-ℤ x is injective for nonzero x

is-injective-neg-ℤ : is-injective neg-ℤ
is-injective-neg-ℤ {x} {y} p = inv (neg-neg-ℤ x) ∙ (ap neg-ℤ p ∙ neg-neg-ℤ y)

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

is-zero-is-zero-neg-ℤ :
  (x : ℤ) → is-zero-ℤ (neg-ℤ x) → is-zero-ℤ x
is-zero-is-zero-neg-ℤ (inr (inl star)) H = refl

is-zero-is-zero-mul-ℤ :
  (x y : ℤ) → is-zero-ℤ (mul-ℤ x y) → coprod (is-zero-ℤ x) (is-zero-ℤ y)
is-zero-is-zero-mul-ℤ (inl x) (inl y) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inl x) (inl y)) ∙ H))
is-zero-is-zero-mul-ℤ (inl x) (inr (inl star)) H = inr refl
is-zero-is-zero-mul-ℤ (inl x) (inr (inr y)) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inl x) (inr (inr y))) ∙ H))
is-zero-is-zero-mul-ℤ (inr (inl star)) y H = inl refl
is-zero-is-zero-mul-ℤ (inr (inr x)) (inl y) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inr (inr x)) (inl y)) ∙ H))
is-zero-is-zero-mul-ℤ (inr (inr x)) (inr (inl star)) H = inr refl
is-zero-is-zero-mul-ℤ (inr (inr x)) (inr (inr y)) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inr (inr x)) (inr (inr y))) ∙ H))

is-injective-mul-ℤ :
  (x : ℤ) → is-nonzero-ℤ x → is-injective (mul-ℤ x)
is-injective-mul-ℤ x f {y} {z} p =
  eq-diff-ℤ
    ( map-left-unit-law-coprod-is-empty
      ( is-zero-ℤ x)
      ( is-zero-ℤ (diff-ℤ y z))
      ( f)
      ( is-zero-is-zero-mul-ℤ x
        ( diff-ℤ y z)
        ( inv (linear-diff-ℤ x y z) ∙ is-zero-diff-ℤ p)))

is-injective-mul-ℤ' :
  (x : ℤ) → is-nonzero-ℤ x → is-injective (mul-ℤ' x)
is-injective-mul-ℤ' x f {y} {z} p =
  is-injective-mul-ℤ x f (commutative-mul-ℤ x y ∙ (p ∙ commutative-mul-ℤ z x))

-- Lemmas about positive integers

is-positive-left-factor-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ (mul-ℤ x y) → is-positive-ℤ y → is-positive-ℤ x
is-positive-left-factor-mul-ℤ {inl x} {inr (inr y)} H K =
  is-positive-eq-ℤ (compute-mul-ℤ (inl x) (inr (inr y))) H
is-positive-left-factor-mul-ℤ {inr (inl star)} {inr (inr y)} H K =
  is-positive-eq-ℤ (compute-mul-ℤ zero-ℤ (inr (inr y))) H
is-positive-left-factor-mul-ℤ {inr (inr x)} {inr (inr y)} H K = star

is-positive-right-factor-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ (mul-ℤ x y) → is-positive-ℤ x → is-positive-ℤ y
is-positive-right-factor-mul-ℤ {x} {y} H =
  is-positive-left-factor-mul-ℤ (is-positive-eq-ℤ (commutative-mul-ℤ x y) H)

-- Lemmas about nonnegative integers

is-nonnegative-mul-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ x → is-nonnegative-ℤ y →
  is-nonnegative-ℤ (mul-ℤ x y)
is-nonnegative-mul-ℤ {inr (inl star)} {y} H K = star
is-nonnegative-mul-ℤ {inr (inr x)} {inr (inl star)} H K =
  is-nonnegative-eq-ℤ (inv (right-zero-law-mul-ℤ (inr (inr x)))) star
is-nonnegative-mul-ℤ {inr (inr x)} {inr (inr y)} H K =
  is-nonnegative-eq-ℤ (inv (compute-mul-ℤ (inr (inr x)) (inr (inr y)))) star

is-nonnegative-left-factor-mul-ℤ :
  {x y : ℤ} →
  is-nonnegative-ℤ (mul-ℤ x y) → is-positive-ℤ y → is-nonnegative-ℤ x
is-nonnegative-left-factor-mul-ℤ {inl x} {inr (inr y)} H K =
  ex-falso (is-nonnegative-eq-ℤ (compute-mul-ℤ (inl x) (inr (inr y))) H)
is-nonnegative-left-factor-mul-ℤ {inr x} {inr y} H K = star

is-nonnegative-right-factor-mul-ℤ :
  {x y : ℤ} →
  is-nonnegative-ℤ (mul-ℤ x y) → is-positive-ℤ x → is-nonnegative-ℤ y
is-nonnegative-right-factor-mul-ℤ {x} {y} H =
  is-nonnegative-left-factor-mul-ℤ
    ( is-nonnegative-eq-ℤ (commutative-mul-ℤ x y) H)

-- We show that ℤ is an ordered ring

preserves-order-add-ℤ' :
  {x y : ℤ} (z : ℤ) → leq-ℤ x y → leq-ℤ (add-ℤ x z) (add-ℤ y z)
preserves-order-add-ℤ' {x} {y} z =
  is-nonnegative-eq-ℤ (inv (right-translation-diff-ℤ y x z))

preserves-order-add-ℤ :
  {x y : ℤ} (z : ℤ) → leq-ℤ x y → leq-ℤ (add-ℤ z x) (add-ℤ z y)
preserves-order-add-ℤ {x} {y} z =
  is-nonnegative-eq-ℤ (inv (left-translation-diff-ℤ y x z))

preserves-leq-add-ℤ :
  {a b c d : ℤ} → leq-ℤ a b → leq-ℤ c d → leq-ℤ (add-ℤ a c) (add-ℤ b d)
preserves-leq-add-ℤ {a} {b} {c} {d} H K =
  trans-leq-ℤ
    ( add-ℤ a c)
    ( add-ℤ b c)
    ( add-ℤ b d)
    ( preserves-order-add-ℤ' {a} {b} c H)
    ( preserves-order-add-ℤ b K)

reflects-order-add-ℤ' :
  {x y z : ℤ} → leq-ℤ (add-ℤ x z) (add-ℤ y z) → leq-ℤ x y
reflects-order-add-ℤ' {x} {y} {z} =
  is-nonnegative-eq-ℤ (right-translation-diff-ℤ y x z)

reflects-order-add-ℤ :
  {x y z : ℤ} → leq-ℤ (add-ℤ z x) (add-ℤ z y) → leq-ℤ x y
reflects-order-add-ℤ {x} {y} {z} =
  is-nonnegative-eq-ℤ (left-translation-diff-ℤ y x z)

preserves-leq-mul-ℤ :
  (x y z : ℤ) → is-nonnegative-ℤ z → leq-ℤ x y → leq-ℤ (mul-ℤ z x) (mul-ℤ z y)
preserves-leq-mul-ℤ x y (inr (inl star)) star K = star
preserves-leq-mul-ℤ x y (inr (inr zero-ℕ)) star K = K
preserves-leq-mul-ℤ x y (inr (inr (succ-ℕ n))) star K =
  preserves-leq-add-ℤ {x} {y}
    { mul-ℤ (inr (inr n)) x}
    { mul-ℤ (inr (inr n)) y}
    ( K)
    ( preserves-leq-mul-ℤ x y (inr (inr n)) star K)

preserves-leq-mul-ℤ' :
  (x y z : ℤ) → is-nonnegative-ℤ z → leq-ℤ x y → leq-ℤ (mul-ℤ x z) (mul-ℤ y z)
preserves-leq-mul-ℤ' x y z H K =
  concatenate-eq-leq-eq-ℤ
    ( commutative-mul-ℤ x z)
    ( preserves-leq-mul-ℤ x y z H K)
    ( commutative-mul-ℤ z y)

-- We define the divisibility relation on ℤ

div-ℤ : ℤ → ℤ → UU lzero
div-ℤ d x = Σ ℤ (λ k → Id (mul-ℤ k d) x)

-- The divisibility relation is a preorder

refl-div-ℤ : (x : ℤ) → div-ℤ x x
pr1 (refl-div-ℤ x) = one-ℤ
pr2 (refl-div-ℤ x) = left-unit-law-mul-ℤ x

trans-div-ℤ :
  (x y z : ℤ) → div-ℤ x y → div-ℤ y z → div-ℤ x z
pr1 (trans-div-ℤ x y z (pair d p) (pair e q)) = mul-ℤ e d
pr2 (trans-div-ℤ x y z (pair d p) (pair e q)) =
  ( associative-mul-ℤ e d x) ∙
    ( ( ap (mul-ℤ e) p) ∙
      ( q))

-- Basic properties of divisibility

div-one-ℤ : (x : ℤ) → div-ℤ one-ℤ x
pr1 (div-one-ℤ x) = x
pr2 (div-one-ℤ x) = right-unit-law-mul-ℤ x

div-zero-ℤ : (x : ℤ) → div-ℤ x zero-ℤ
pr1 (div-zero-ℤ x) = zero-ℤ
pr2 (div-zero-ℤ x) = left-zero-law-mul-ℤ x

is-zero-div-zero-ℤ :
  (x : ℤ) → div-ℤ zero-ℤ x → is-zero-ℤ x
is-zero-div-zero-ℤ x (pair d p) = inv p ∙ right-zero-law-mul-ℤ d

div-add-ℤ : (x y z : ℤ) → div-ℤ x y → div-ℤ x z → div-ℤ x (add-ℤ y z)
pr1 (div-add-ℤ x y z (pair d p) (pair e q)) = add-ℤ d e
pr2 (div-add-ℤ x y z (pair d p) (pair e q)) =
  ( right-distributive-mul-add-ℤ d e x) ∙
  ( ap-add-ℤ p q)

div-neg-ℤ : (x y : ℤ) → div-ℤ x y → div-ℤ x (neg-ℤ y)
pr1 (div-neg-ℤ x y (pair d p)) = neg-ℤ d
pr2 (div-neg-ℤ x y (pair d p)) = left-negative-law-mul-ℤ d x ∙ ap neg-ℤ p

-- Comparison of divisibility on ℕ and on ℤ

div-int-div-ℕ :
  {x y : ℕ} → div-ℕ x y → div-ℤ (int-ℕ x) (int-ℕ y)
pr1 (div-int-div-ℕ {x} {y} (pair d p)) = int-ℕ d
pr2 (div-int-div-ℕ {x} {y} (pair d p)) = mul-int-ℕ d x ∙ ap int-ℕ p

int-abs-is-nonnegative-ℤ :
  (x : ℤ) → is-nonnegative-ℤ x → Id (int-abs-ℤ x) x
int-abs-is-nonnegative-ℤ (inr (inl star)) star = refl
int-abs-is-nonnegative-ℤ (inr (inr x)) star = refl

div-div-int-ℕ :
  {x y : ℕ} → div-ℤ (int-ℕ x) (int-ℕ y) → div-ℕ x y
div-div-int-ℕ {zero-ℕ} {y} (pair d p) =
  div-eq-ℕ zero-ℕ y
    ( inv (is-injective-int-ℕ (is-zero-div-zero-ℤ (int-ℕ y) (pair d p))))
pr1 (div-div-int-ℕ {succ-ℕ x} {y} (pair d p)) = abs-ℤ d
pr2 (div-div-int-ℕ {succ-ℕ x} {y} (pair d p)) =
  is-injective-int-ℕ
    ( ( inv (mul-int-ℕ (abs-ℤ d) (succ-ℕ x))) ∙
      ( ( ap
          ( mul-ℤ' (inr (inr x)))
          { int-abs-ℤ d}
          { d}
          ( int-abs-is-nonnegative-ℤ d
            ( is-nonnegative-left-factor-mul-ℤ
              { d}
              { inr (inr x)}
              ( is-nonnegative-eq-ℤ (inv p) (is-nonnegative-int-ℕ y))
              ( star)))) ∙
        ( p)))

-- We introduce units

is-unit-ℤ : ℤ → UU lzero
is-unit-ℤ x = div-ℤ x one-ℤ

unit-ℤ : UU lzero
unit-ℤ = Σ ℤ is-unit-ℤ

int-unit-ℤ : unit-ℤ → ℤ
int-unit-ℤ = pr1

is-unit-int-unit-ℤ : (x : unit-ℤ) → is-unit-ℤ (int-unit-ℤ x)
is-unit-int-unit-ℤ = pr2

div-is-unit-ℤ :
  (x y : ℤ) → is-unit-ℤ x → div-ℤ x y
pr1 (div-is-unit-ℤ x y (pair d p)) = mul-ℤ y d
pr2 (div-is-unit-ℤ x y (pair d p)) =
  associative-mul-ℤ y d x ∙ (ap (mul-ℤ y) p ∙ right-unit-law-mul-ℤ y)

-- An integer is a unit if and only if it is 1 or -1.

is-one-or-neg-one-ℤ : ℤ → UU lzero
is-one-or-neg-one-ℤ x = coprod (is-one-ℤ x) (is-neg-one-ℤ x)

is-unit-one-ℤ : is-unit-ℤ one-ℤ
is-unit-one-ℤ = refl-div-ℤ one-ℤ

one-unit-ℤ : unit-ℤ
pr1 one-unit-ℤ = one-ℤ
pr2 one-unit-ℤ = is-unit-one-ℤ

is-unit-is-one-ℤ :
  (x : ℤ) → is-one-ℤ x → is-unit-ℤ x
is-unit-is-one-ℤ .one-ℤ refl = is-unit-one-ℤ

is-unit-neg-one-ℤ : is-unit-ℤ neg-one-ℤ
pr1 is-unit-neg-one-ℤ = neg-one-ℤ
pr2 is-unit-neg-one-ℤ = refl

neg-one-unit-ℤ : unit-ℤ
pr1 neg-one-unit-ℤ = neg-one-ℤ
pr2 neg-one-unit-ℤ = is-unit-neg-one-ℤ

is-unit-is-neg-one-ℤ :
  (x : ℤ) → is-neg-one-ℤ x → is-unit-ℤ x
is-unit-is-neg-one-ℤ .neg-one-ℤ refl = is-unit-neg-one-ℤ

is-unit-is-one-or-neg-one-ℤ :
  (x : ℤ) → is-one-or-neg-one-ℤ x → is-unit-ℤ x
is-unit-is-one-or-neg-one-ℤ x (inl p) = is-unit-is-one-ℤ x p
is-unit-is-one-or-neg-one-ℤ x (inr p) = is-unit-is-neg-one-ℤ x p

is-one-or-neg-one-is-unit-ℤ :
  (x : ℤ) → is-unit-ℤ x → is-one-or-neg-one-ℤ x
is-one-or-neg-one-is-unit-ℤ (inl zero-ℕ) (pair d p) = inr refl
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inl zero-ℕ) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ neg-one-ℤ (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inl (succ-ℕ d)) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ (inl (succ-ℕ d)) (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inl star)) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ zero-ℤ (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inr zero-ℕ)) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ one-ℤ (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (pair (inr (inr (succ-ℕ d))) p) =
  ex-falso
    ( Eq-eq-ℤ (inv p ∙ compute-mul-ℤ (inr (inr (succ-ℕ d))) (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inr (inl star)) (pair d p) =
  ex-falso (Eq-eq-ℤ (inv (right-zero-law-mul-ℤ d) ∙ p))
is-one-or-neg-one-is-unit-ℤ (inr (inr zero-ℕ)) (pair d p) = inl refl
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inl zero-ℕ) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ neg-one-ℤ (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inl (succ-ℕ d)) p) =
  ex-falso
    ( Eq-eq-ℤ (inv p ∙ compute-mul-ℤ (inl (succ-ℕ d)) (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inr (inl star)) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ zero-ℤ (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (pair (inr (inr zero-ℕ)) p) =
  ex-falso (Eq-eq-ℤ (inv p ∙ compute-mul-ℤ one-ℤ (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ
  (inr (inr (succ-ℕ x))) (pair (inr (inr (succ-ℕ d))) p) =
  ex-falso
    ( Eq-eq-ℤ
      ( inv p ∙ compute-mul-ℤ (inr (inr (succ-ℕ d))) (inr (inr (succ-ℕ x)))))

idempotent-is-unit-ℤ : {x : ℤ} → is-unit-ℤ x → Id (mul-ℤ x x) one-ℤ
idempotent-is-unit-ℤ {x} H =
  f (is-one-or-neg-one-is-unit-ℤ x H)
  where
  f : is-one-or-neg-one-ℤ x → Id (mul-ℤ x x) one-ℤ
  f (inl refl) = refl
  f (inr refl) = refl

-- The product xy is a unit if and only if both x and y are units

is-unit-mul-ℤ :
  (x y : ℤ) → is-unit-ℤ x → is-unit-ℤ y → is-unit-ℤ (mul-ℤ x y)
pr1 (is-unit-mul-ℤ x y (pair d p) (pair e q)) = mul-ℤ e d
pr2 (is-unit-mul-ℤ x y (pair d p) (pair e q)) =
  ( associative-mul-ℤ e d (mul-ℤ x y)) ∙
    ( ( ap
        ( mul-ℤ e)
        ( ( inv (associative-mul-ℤ d x y)) ∙
          ( ap (mul-ℤ' y) p))) ∙
      ( q))

mul-unit-ℤ : unit-ℤ → unit-ℤ → unit-ℤ
pr1 (mul-unit-ℤ (pair x H) (pair y K)) = mul-ℤ x y
pr2 (mul-unit-ℤ (pair x H) (pair y K)) = is-unit-mul-ℤ x y H K

is-unit-left-factor-mul-ℤ :
  (x y : ℤ) → is-unit-ℤ (mul-ℤ x y) → is-unit-ℤ x
pr1 (is-unit-left-factor-mul-ℤ x y (pair d p)) = mul-ℤ d y
pr2 (is-unit-left-factor-mul-ℤ x y (pair d p)) =
  associative-mul-ℤ d y x ∙ (ap (mul-ℤ d) (commutative-mul-ℤ y x) ∙ p)

is-unit-right-factor-ℤ :
  (x y : ℤ) → is-unit-ℤ (mul-ℤ x y) → is-unit-ℤ y
is-unit-right-factor-ℤ x y (pair d p) =
  is-unit-left-factor-mul-ℤ y x
    ( pair d (ap (mul-ℤ d) (commutative-mul-ℤ y x) ∙ p))

-- We introduce the equivalence relation ux = y, where u is a unit

{- The relation presim-unit-ℤ would be an equivalence relation, except it is not
   valued in the propositions. Indeed presim-unit-ℤ zero-ℤ zero-ℤ is not a
   proposition. -}
presim-unit-ℤ : ℤ → ℤ → UU lzero
presim-unit-ℤ x y = Σ unit-ℤ (λ u → Id (mul-ℤ (pr1 u) x) y)

{- We could define sim-unit-ℤ x y to be the propositional truncation of
   presim-unit-ℤ, but that's a waste because presim-unit-ℤ x y is only not a 
   proposition when both x and y are zero. -}
sim-unit-ℤ : ℤ → ℤ → UU lzero
sim-unit-ℤ x y = ¬ (is-zero-ℤ x × is-zero-ℤ y) → presim-unit-ℤ x y

-- The relations presim-unit-ℤ and sim-unit-ℤ are logially equivalent

sim-unit-presim-unit-ℤ :
  {x y : ℤ} → presim-unit-ℤ x y → sim-unit-ℤ x y
sim-unit-presim-unit-ℤ {x} {y} H f = H

presim-unit-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → presim-unit-ℤ x y
presim-unit-sim-unit-ℤ {inl x} {inl y} H = H (λ t → Eq-eq-ℤ (pr1 t))
presim-unit-sim-unit-ℤ {inl x} {inr y} H = H (λ t → Eq-eq-ℤ (pr1 t))
presim-unit-sim-unit-ℤ {inr x} {inl y} H = H (λ t → Eq-eq-ℤ (pr2 t))
pr1 (presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inl star)} H) = one-unit-ℤ
pr2 (presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inl star)} H) = refl
presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inr y)} H =
  H (λ t → Eq-eq-ℤ (pr2 t))
presim-unit-sim-unit-ℤ {inr (inr x)} {inr (inl star)} H =
  H (λ t → Eq-eq-ℤ (pr1 t))
presim-unit-sim-unit-ℤ {inr (inr x)} {inr (inr y)} H =
  H (λ t → Eq-eq-ℤ (pr1 t))

-- The relations presim-unit-ℤ and sim-unit-ℤ relate zero-ℤ only to itself

is-nonzero-presim-unit-ℤ :
  {x y : ℤ} → presim-unit-ℤ x y → is-nonzero-ℤ x → is-nonzero-ℤ y
is-nonzero-presim-unit-ℤ {x} {y} (pair (pair v (pair u α)) β) f p =
  Eq-eq-ℤ (ap (mul-ℤ' u) (inv q) ∙ (commutative-mul-ℤ v u ∙ α))
  where
  q : Id v zero-ℤ
  q = is-injective-mul-ℤ' x f {v} {zero-ℤ} (β ∙ p)
  
is-nonzero-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → is-nonzero-ℤ x → is-nonzero-ℤ y
is-nonzero-sim-unit-ℤ H f =
  is-nonzero-presim-unit-ℤ (H (f ∘ pr1)) f

is-zero-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → is-zero-ℤ x → is-zero-ℤ y
is-zero-sim-unit-ℤ {x} {y} H p =
  dn-elim-is-decidable
    ( is-zero-ℤ y)
    ( has-decidable-equality-ℤ y zero-ℤ)
    ( λ g → g (inv (β g) ∙ (ap (mul-ℤ (u g)) p ∙ right-zero-law-mul-ℤ (u g))))
  where
  K : is-nonzero-ℤ y → presim-unit-ℤ x y
  K g = H (λ {(pair u v) → g v})
  u : is-nonzero-ℤ y → ℤ
  u g = pr1 (pr1 (K g))
  v : is-nonzero-ℤ y → ℤ
  v g = pr1 (pr2 (pr1 (K g)))
  β : (g : is-nonzero-ℤ y) → Id (mul-ℤ (u g) x) y
  β g = pr2 (K g)

-- The relations presim-unit-ℤ and sim-unit-ℤ are equivalence relations

refl-presim-unit-ℤ : (x : ℤ) → presim-unit-ℤ x x
pr1 (refl-presim-unit-ℤ x) = one-unit-ℤ
pr2 (refl-presim-unit-ℤ x) = left-unit-law-mul-ℤ x

refl-sim-unit-ℤ : (x : ℤ) → sim-unit-ℤ x x
refl-sim-unit-ℤ x f = refl-presim-unit-ℤ x

presim-unit-eq-ℤ : {x y : ℤ} → Id x y → presim-unit-ℤ x y
presim-unit-eq-ℤ {x} refl = refl-presim-unit-ℤ x

sim-unit-eq-ℤ : {x y : ℤ} → Id x y → sim-unit-ℤ x y
sim-unit-eq-ℤ {x} refl = refl-sim-unit-ℤ x

symm-presim-unit-ℤ : {x y : ℤ} → presim-unit-ℤ x y → presim-unit-ℤ y x
symm-presim-unit-ℤ {x} {y} (pair (pair u H) p) =
  f (is-one-or-neg-one-is-unit-ℤ u H)
  where
  f : is-one-or-neg-one-ℤ u → presim-unit-ℤ y x
  pr1 (f (inl refl)) = one-unit-ℤ
  pr2 (f (inl refl)) = inv p
  pr1 (f (inr refl)) = neg-one-unit-ℤ
  pr2 (f (inr refl)) = inv (inv (neg-neg-ℤ x) ∙ ap (mul-ℤ neg-one-ℤ) p)

symm-sim-unit-ℤ : {x y : ℤ} → sim-unit-ℤ x y → sim-unit-ℤ y x
symm-sim-unit-ℤ {x} {y} H f =
  symm-presim-unit-ℤ (H (λ p → f (pair (pr2 p) (pr1 p))))

is-nonzero-sim-unit-ℤ' :
  {x y : ℤ} → sim-unit-ℤ x y → is-nonzero-ℤ y → is-nonzero-ℤ x
is-nonzero-sim-unit-ℤ' H = is-nonzero-sim-unit-ℤ (symm-sim-unit-ℤ H)

is-zero-sim-unit-ℤ' :
  {x y : ℤ} → sim-unit-ℤ x y → is-zero-ℤ y → is-zero-ℤ x
is-zero-sim-unit-ℤ' H = is-zero-sim-unit-ℤ (symm-sim-unit-ℤ H)

trans-presim-unit-ℤ :
  (x y z : ℤ) → presim-unit-ℤ x y → presim-unit-ℤ y z → presim-unit-ℤ x z
trans-presim-unit-ℤ x y z (pair (pair u H) p) (pair (pair v K) q) =
  f (is-one-or-neg-one-is-unit-ℤ u H) (is-one-or-neg-one-is-unit-ℤ v K)
  where
  f : is-one-or-neg-one-ℤ u → is-one-or-neg-one-ℤ v → presim-unit-ℤ x z
  pr1 (f (inl refl) (inl refl)) = one-unit-ℤ
  pr2 (f (inl refl) (inl refl)) = p ∙ q
  pr1 (f (inl refl) (inr refl)) = neg-one-unit-ℤ
  pr2 (f (inl refl) (inr refl)) = ap neg-ℤ p ∙ q
  pr1 (f (inr refl) (inl refl)) = neg-one-unit-ℤ
  pr2 (f (inr refl) (inl refl)) = p ∙ q
  pr1 (f (inr refl) (inr refl)) = one-unit-ℤ
  pr2 (f (inr refl) (inr refl)) = inv (neg-neg-ℤ x) ∙ (ap neg-ℤ p ∙ q)

trans-sim-unit-ℤ :
  (x y z : ℤ) → sim-unit-ℤ x y → sim-unit-ℤ y z → sim-unit-ℤ x z
trans-sim-unit-ℤ x y z H K f =
  trans-presim-unit-ℤ x y z
    ( H (λ {(pair p q) → f (pair p (is-zero-sim-unit-ℤ K q))}))
    ( K (λ {(pair p q) → f (pair (is-zero-sim-unit-ℤ' H p) q)}))

-- We show that sim-unit-ℤ x y holds if and only if x|y and y|x

antisymmetric-div-ℤ :
  (x y : ℤ) → div-ℤ x y → div-ℤ y x → sim-unit-ℤ x y
antisymmetric-div-ℤ x y (pair d p) (pair e q) H =
  f (is-decidable-is-zero-ℤ x)
  where
  f : is-decidable (is-zero-ℤ x) → presim-unit-ℤ x y
  f (inl refl) = presim-unit-eq-ℤ (inv (right-zero-law-mul-ℤ d) ∙ p)
  pr1 (pr1 (f (inr g))) = d
  pr1 (pr2 (pr1 (f (inr g)))) = e
  pr2 (pr2 (pr1 (f (inr g)))) =
    is-injective-mul-ℤ x g
      ( ( commutative-mul-ℤ x (mul-ℤ e d)) ∙
        ( ( associative-mul-ℤ e d x) ∙
          ( ( ap (mul-ℤ e) p) ∙
            ( q ∙ inv (right-unit-law-mul-ℤ x)))))
  pr2 (f (inr g)) = p

-- We show that sim-unit-ℤ |x| x holds

sim-unit-abs-ℤ : (x : ℤ) → sim-unit-ℤ (int-abs-ℤ x) x
pr1 (sim-unit-abs-ℤ (inl x) f) = neg-one-unit-ℤ
pr2 (sim-unit-abs-ℤ (inl x) f) = refl
sim-unit-abs-ℤ (inr (inl star)) = refl-sim-unit-ℤ zero-ℤ
sim-unit-abs-ℤ (inr (inr x)) = refl-sim-unit-ℤ (inr (inr x))

div-presim-unit-ℤ :
  {x y x' y' : ℤ} → presim-unit-ℤ x x' → presim-unit-ℤ y y' →
  div-ℤ x y → div-ℤ x' y'
pr1 (div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p)) =
  mul-ℤ (mul-ℤ (int-unit-ℤ v) d) (int-unit-ℤ u)
pr2 (div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p)) =
  ( ap (mul-ℤ (mul-ℤ (mul-ℤ (int-unit-ℤ v) d) (int-unit-ℤ u))) (inv q)) ∙
  ( ( associative-mul-ℤ
      ( mul-ℤ (int-unit-ℤ v) d)
      ( int-unit-ℤ u)
      ( mul-ℤ (int-unit-ℤ u) x)) ∙
    ( ( ap
        ( mul-ℤ (mul-ℤ (int-unit-ℤ v) d))
        ( ( inv (associative-mul-ℤ (int-unit-ℤ u) (int-unit-ℤ u) x)) ∙
          ( ap (mul-ℤ' x) (idempotent-is-unit-ℤ (is-unit-int-unit-ℤ u))))) ∙
      ( ( associative-mul-ℤ (int-unit-ℤ v) d x) ∙
        ( ( ap (mul-ℤ (int-unit-ℤ v)) p) ∙
          ( r)))))

div-sim-unit-ℤ :
  {x y x' y' : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' →
  div-ℤ x y → div-ℤ x' y'
div-sim-unit-ℤ {x} {y} {x'} {y'} H K =
  div-presim-unit-ℤ (presim-unit-sim-unit-ℤ H) (presim-unit-sim-unit-ℤ K)

div-int-abs-div-ℤ :
  {x y : ℤ} → div-ℤ x y → div-ℤ (int-abs-ℤ x) y
div-int-abs-div-ℤ {x} {y} =
  div-sim-unit-ℤ (symm-sim-unit-ℤ (sim-unit-abs-ℤ x)) (refl-sim-unit-ℤ y)

div-div-int-abs-ℤ :
  {x y : ℤ} → div-ℤ (int-abs-ℤ x) y → div-ℤ x y
div-div-int-abs-ℤ {x} {y} =
  div-sim-unit-ℤ (sim-unit-abs-ℤ x) (refl-sim-unit-ℤ y)

-- Modular arithmetic on ℤ

ℤ-Mod : (k : ℕ) → UU lzero
ℤ-Mod zero-ℕ = ℤ
ℤ-Mod (succ-ℕ k) = Fin (succ-ℕ k)

zero-ℤ-Mod : (k : ℕ) → ℤ-Mod k
zero-ℤ-Mod zero-ℕ = zero-ℤ
zero-ℤ-Mod (succ-ℕ k) = zero-Fin

neg-one-ℤ-Mod : (k : ℕ) → ℤ-Mod k
neg-one-ℤ-Mod zero-ℕ = neg-one-ℤ
neg-one-ℤ-Mod (succ-ℕ k) = neg-one-Fin

one-ℤ-Mod : (k : ℕ) → ℤ-Mod k
one-ℤ-Mod zero-ℕ = one-ℤ
one-ℤ-Mod (succ-ℕ k) = one-Fin

is-zero-ℤ-Mod : (k : ℕ) → ℤ-Mod k → UU lzero
is-zero-ℤ-Mod k x = Id x (zero-ℤ-Mod k)

is-nonzero-ℤ-Mod : (k : ℕ) → ℤ-Mod k → UU lzero
is-nonzero-ℤ-Mod k x = ¬ (is-zero-ℤ-Mod k x)

succ-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k
succ-ℤ-Mod zero-ℕ = succ-ℤ
succ-ℤ-Mod (succ-ℕ k) = succ-Fin

pred-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k
pred-ℤ-Mod zero-ℕ = pred-ℤ
pred-ℤ-Mod (succ-ℕ k) = pred-Fin

issec-pred-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → Id (succ-ℤ-Mod k (pred-ℤ-Mod k x)) x
issec-pred-ℤ-Mod zero-ℕ = issec-pred-ℤ
issec-pred-ℤ-Mod (succ-ℕ k) = issec-pred-Fin

isretr-pred-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → Id (pred-ℤ-Mod k (succ-ℤ-Mod k x)) x
isretr-pred-ℤ-Mod zero-ℕ = isretr-pred-ℤ
isretr-pred-ℤ-Mod (succ-ℕ k) = isretr-pred-Fin

add-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
add-ℤ-Mod zero-ℕ = add-ℤ
add-ℤ-Mod (succ-ℕ k) = add-Fin

add-ℤ-Mod' : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
add-ℤ-Mod' k x y = add-ℤ-Mod k y x

ap-add-ℤ-Mod :
  (k : ℕ) {x x' y y' : ℤ-Mod k} →
  Id x x' → Id y y' → Id (add-ℤ-Mod k x y) (add-ℤ-Mod k x' y')
ap-add-ℤ-Mod k p q = ap-binary (add-ℤ-Mod k) p q

is-injective-add-ℤ-Mod : (k : ℕ) (x : ℤ-Mod k) → is-injective (add-ℤ-Mod k x)
is-injective-add-ℤ-Mod zero-ℕ = is-injective-add-ℤ
is-injective-add-ℤ-Mod (succ-ℕ k) = is-injective-add-Fin

is-injective-add-ℤ-Mod' : (k : ℕ) (x : ℤ-Mod k) → is-injective (add-ℤ-Mod' k x)
is-injective-add-ℤ-Mod' zero-ℕ = is-injective-add-ℤ'
is-injective-add-ℤ-Mod' (succ-ℕ k) = is-injective-add-Fin'

neg-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k
neg-ℤ-Mod zero-ℕ = neg-ℤ
neg-ℤ-Mod (succ-ℕ k) = neg-Fin

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

mul-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
mul-ℤ-Mod zero-ℕ = mul-ℤ
mul-ℤ-Mod (succ-ℕ k) = mul-Fin

mul-ℤ-Mod' : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → ℤ-Mod k
mul-ℤ-Mod' k x y = mul-ℤ-Mod k y x

ap-mul-ℤ-Mod :
  (k : ℕ) {x x' y y' : ℤ-Mod k} →
  Id x x' → Id y y' → Id (mul-ℤ-Mod k x y) (mul-ℤ-Mod k x' y')
ap-mul-ℤ-Mod k p q = ap-binary (mul-ℤ-Mod k) p q

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

mod-ℕ : (k : ℕ) → ℕ → ℤ-Mod k
mod-ℕ zero-ℕ x = int-ℕ x
mod-ℕ (succ-ℕ k) x = mod-succ-ℕ k x

mod-ℤ : (k : ℕ) → ℤ → ℤ-Mod k
mod-ℤ zero-ℕ x = x
mod-ℤ (succ-ℕ k) (inl x) = neg-Fin (mod-succ-ℕ k (succ-ℕ x))
mod-ℤ (succ-ℕ k) (inr (inl x)) = zero-Fin
mod-ℤ (succ-ℕ k) (inr (inr x)) = mod-succ-ℕ k (succ-ℕ x)

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
    ( inv (is-add-neg-one-pred-Fin zero-Fin)))
preserves-predecessor-mod-ℤ (succ-ℕ k) (inr (inr zero-ℕ)) =
  inv
    ( ( ap pred-Fin (preserves-successor-mod-ℤ (succ-ℕ k) zero-ℤ)) ∙
      ( isretr-pred-Fin zero-Fin))
preserves-predecessor-mod-ℤ (succ-ℕ k) (inr (inr (succ-ℕ x))) =
  inv (isretr-pred-Fin (succ-Fin (mod-succ-ℕ k x)))

mod-neg-one-ℤ : (k : ℕ) → Id (mod-ℤ k neg-one-ℤ) (neg-one-ℤ-Mod k)
mod-neg-one-ℤ zero-ℕ = refl
mod-neg-one-ℤ (succ-ℕ k) =
  ( neg-succ-Fin zero-Fin) ∙
  ( ( ap pred-Fin neg-zero-Fin) ∙
    ( ( is-add-neg-one-pred-Fin zero-Fin) ∙
      ( left-unit-law-add-Fin neg-one-Fin)))

preserves-add-mod-ℤ :
  (k : ℕ) (x y : ℤ) →
  Id (mod-ℤ k (add-ℤ x y)) (add-ℤ-Mod k (mod-ℤ k x) (mod-ℤ k y))
preserves-add-mod-ℤ zero-ℕ x y = refl
preserves-add-mod-ℤ (succ-ℕ k) (inl zero-ℕ) y =
  ( preserves-predecessor-mod-ℤ (succ-ℕ k) y) ∙
  ( ( is-add-neg-one-pred-Fin (mod-ℤ (succ-ℕ k) y)) ∙
    ( ( commutative-add-Fin (mod-ℤ (succ-ℕ k) y) neg-one-Fin) ∙
      ( ap (add-Fin' (mod-ℤ (succ-ℕ k) y)) (inv (mod-neg-one-ℤ (succ-ℕ k))))))
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

cong-ℤ : ℤ → ℤ → ℤ → UU lzero
cong-ℤ k x y = div-ℤ k (diff-ℤ x y)

is-indiscrete-cong-ℤ : (k : ℤ) → is-unit-ℤ k → (x y : ℤ) → cong-ℤ k x y
is-indiscrete-cong-ℤ k H x y = div-is-unit-ℤ k (diff-ℤ x y) H

is-discrete-cong-ℤ : (k : ℤ) → is-zero-ℤ k → (x y : ℤ) → cong-ℤ k x y → Id x y
is-discrete-cong-ℤ .zero-ℤ refl x y K =
  eq-diff-ℤ (is-zero-div-zero-ℤ (diff-ℤ x y) K)

refl-cong-ℤ : (k x : ℤ) → cong-ℤ k x x
pr1 (refl-cong-ℤ k x) = zero-ℤ
pr2 (refl-cong-ℤ k x) = left-zero-law-mul-ℤ k ∙ inv (is-zero-diff-ℤ' x)

symmetric-cong-ℤ : (k x y : ℤ) → cong-ℤ k x y → cong-ℤ k y x
pr1 (symmetric-cong-ℤ k x y (pair d p)) = neg-ℤ d
pr2 (symmetric-cong-ℤ k x y (pair d p)) =
  ( left-negative-law-mul-ℤ d k) ∙
  ( ( ap neg-ℤ p) ∙
    ( distributive-neg-diff-ℤ x y))

transitive-cong-ℤ : (k x y z : ℤ) → cong-ℤ k x y → cong-ℤ k y z → cong-ℤ k x z
pr1 (transitive-cong-ℤ k x y z (pair d p) (pair e q)) = add-ℤ d e
pr2 (transitive-cong-ℤ k x y z (pair d p) (pair e q)) =
  ( right-distributive-mul-add-ℤ d e k) ∙
  ( ( ap-add-ℤ p q) ∙
    ( triangle-diff-ℤ x y z))

concatenate-eq-cong-ℤ :
  {k x x' y : ℤ} → Id x x' → cong-ℤ k x' y → cong-ℤ k x y
concatenate-eq-cong-ℤ refl = id

concatenate-cong-eq-ℤ :
  {k x y y' : ℤ} → cong-ℤ k x y → Id y y' → cong-ℤ k x y'
concatenate-cong-eq-ℤ H refl = H

concatenate-eq-cong-eq-ℤ :
  {k x x' y' y : ℤ} → Id x x' → cong-ℤ k x' y' → Id y' y → cong-ℤ k x y
concatenate-eq-cong-eq-ℤ refl H refl = H

concatenate-cong-eq-cong-ℤ :
  {k x y y' z : ℤ} → cong-ℤ k x y → Id y y' → cong-ℤ k y' z → cong-ℤ k x z
concatenate-cong-eq-cong-ℤ {k} {x} {y} {.y} {z} H refl K =
  transitive-cong-ℤ k x y z H K

cong-cong-neg-ℤ : (k x y : ℤ) → cong-ℤ k (neg-ℤ x) (neg-ℤ y) → cong-ℤ k x y
pr1 (cong-cong-neg-ℤ k x y (pair d p)) = neg-ℤ d
pr2 (cong-cong-neg-ℤ k x y (pair d p)) =
  ( left-negative-law-mul-ℤ d k) ∙
  ( ( ap neg-ℤ p) ∙
    ( ( distributive-neg-add-ℤ (neg-ℤ x) (neg-ℤ (neg-ℤ y))) ∙
      ( ap-add-ℤ (neg-neg-ℤ x) (neg-neg-ℤ (neg-ℤ y)))))

cong-neg-cong-ℤ : (k x y : ℤ) → cong-ℤ k x y → cong-ℤ k (neg-ℤ x) (neg-ℤ y)
pr1 (cong-neg-cong-ℤ k x y (pair d p)) = neg-ℤ d
pr2 (cong-neg-cong-ℤ k x y (pair d p)) =
  ( left-negative-law-mul-ℤ d k) ∙
  ( ( ap neg-ℤ p) ∙
    ( distributive-neg-add-ℤ x (neg-ℤ y)))

-- The distance between two integers

dist-ℤ : ℤ → ℤ → ℕ
dist-ℤ x y = abs-ℤ (diff-ℤ x y)

ap-dist-ℤ :
  {x x' y y' : ℤ} (p : Id x x') (q : Id y y') → Id (dist-ℤ x y) (dist-ℤ x' y')
ap-dist-ℤ p q = ap-binary dist-ℤ p q

left-zero-law-dist-ℤ : (x : ℤ) → Id (dist-ℤ zero-ℤ x) (abs-ℤ x)
left-zero-law-dist-ℤ x = ap abs-ℤ (left-zero-law-diff-ℤ x) ∙ abs-neg-ℤ x

right-zero-law-dist-ℤ : (x : ℤ) → Id (dist-ℤ x zero-ℤ) (abs-ℤ x)
right-zero-law-dist-ℤ x = ap abs-ℤ (right-zero-law-diff-ℤ x)

diff-succ-ℤ : (x y : ℤ) → Id (diff-ℤ (succ-ℤ x) (succ-ℤ y)) (diff-ℤ x y)
diff-succ-ℤ x y =
  ( ap (add-ℤ (succ-ℤ x)) (neg-succ-ℤ y)) ∙
  ( ( left-successor-law-add-ℤ x (pred-ℤ (neg-ℤ y))) ∙
    ( ( ap succ-ℤ (right-predecessor-law-add-ℤ x (neg-ℤ y))) ∙
      ( issec-pred-ℤ (diff-ℤ x y))))

int-succ-ℕ : (x : ℕ) → Id (int-ℕ (succ-ℕ x)) (succ-ℤ (int-ℕ x))
int-succ-ℕ zero-ℕ = refl
int-succ-ℕ (succ-ℕ x) = refl

dist-int-ℕ :
  (x y : ℕ) → Id (dist-ℤ (int-ℕ x) (int-ℕ y)) (dist-ℕ x y)
dist-int-ℕ zero-ℕ zero-ℕ = refl
dist-int-ℕ zero-ℕ (succ-ℕ y) = left-zero-law-dist-ℤ (int-ℕ (succ-ℕ y))
dist-int-ℕ (succ-ℕ x) zero-ℕ = right-zero-law-dist-ℤ (int-ℕ (succ-ℕ x))
dist-int-ℕ (succ-ℕ x) (succ-ℕ y) =
  ( ( ap-dist-ℤ (int-succ-ℕ x) (int-succ-ℕ y)) ∙
    ( ap abs-ℤ (diff-succ-ℤ (int-ℕ x) (int-ℕ y)))) ∙
  ( dist-int-ℕ x y)

cong-int-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℤ (int-ℕ k) (int-ℕ x) (int-ℕ y)
cong-int-cong-ℕ k x y H =
  div-sim-unit-ℤ
    ( refl-sim-unit-ℤ (int-ℕ k))
    ( sim-unit-abs-ℤ (diff-ℤ (int-ℕ x) (int-ℕ y)))
    ( tr
      ( div-ℤ (int-ℕ k))
      ( inv (ap int-ℕ (dist-int-ℕ x y)))
      ( div-int-div-ℕ H))

cong-cong-int-ℕ :
  (k x y : ℕ) → cong-ℤ (int-ℕ k) (int-ℕ x) (int-ℕ y) → cong-ℕ k x y
cong-cong-int-ℕ k x y H =
  div-div-int-ℕ
    ( tr
      ( div-ℤ (int-ℕ k))
      ( ap int-ℕ (dist-int-ℕ x y))
      ( div-sim-unit-ℤ
        ( refl-sim-unit-ℤ (int-ℕ k))
        ( symm-sim-unit-ℤ (sim-unit-abs-ℤ (diff-ℤ (int-ℕ x) (int-ℕ y))))
        ( H)))

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
    { int-ℕ (succ-ℕ k)}
    { int-ℤ-Mod (succ-ℕ k) (mod-ℤ (succ-ℕ k) (inl x))}
    { int-ℕ (nat-Fin (mul-Fin neg-one-Fin (mod-succ-ℕ k (succ-ℕ x))))}
    { inl x}
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
cong-int-mod-ℤ (succ-ℕ k) (inr (inl star)) = cong-int-mod-ℕ (succ-ℕ k) zero-ℕ
cong-int-mod-ℤ (succ-ℕ k) (inr (inr x)) = cong-int-mod-ℕ (succ-ℕ k) (succ-ℕ x)

-- We introduce the condition on ℤ of being a gcd.

is-common-divisor-ℤ : ℤ → ℤ → ℤ → UU lzero
is-common-divisor-ℤ x y d = (div-ℤ d x) × (div-ℤ d y)

is-gcd-ℤ : ℤ → ℤ → ℤ → UU lzero
is-gcd-ℤ x y d =
  is-nonnegative-ℤ d × ((k : ℤ) → is-common-divisor-ℤ x y k ↔ div-ℤ k d)

-- We relate divisibility and being a gcd on ℕ and on ℤ

is-common-divisor-int-is-common-divisor-ℕ :
  {x y d : ℕ} →
  is-common-divisor-ℕ x y d → is-common-divisor-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d)
is-common-divisor-int-is-common-divisor-ℕ =
  map-prod div-int-div-ℕ div-int-div-ℕ

is-common-divisor-is-common-divisor-int-ℕ :
  {x y d : ℕ} →
  is-common-divisor-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d) → is-common-divisor-ℕ x y d
is-common-divisor-is-common-divisor-int-ℕ {x} {y} {d} =
  map-prod div-div-int-ℕ div-div-int-ℕ

is-common-divisor-sim-unit-ℤ :
  {x x' y y' d d' : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' → sim-unit-ℤ d d' →
  is-common-divisor-ℤ x y d → is-common-divisor-ℤ x' y' d'
is-common-divisor-sim-unit-ℤ H K L =
  map-prod (div-sim-unit-ℤ L H) (div-sim-unit-ℤ L K)

is-gcd-sim-unit-ℤ :
  {x x' y y' d : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' →
  is-gcd-ℤ x y d → is-gcd-ℤ x' y' d
pr1 (is-gcd-sim-unit-ℤ H K (pair x _)) = x
pr1 (pr2 (is-gcd-sim-unit-ℤ H K (pair _ G)) k) =
  ( pr1 (G k)) ∘
  ( is-common-divisor-sim-unit-ℤ
    ( symm-sim-unit-ℤ H)
    ( symm-sim-unit-ℤ K)
    ( refl-sim-unit-ℤ k))
pr2 (pr2 (is-gcd-sim-unit-ℤ H K (pair _ G)) k) =
  ( is-common-divisor-sim-unit-ℤ H K (refl-sim-unit-ℤ k)) ∘
  ( pr2 (G k))

is-common-divisor-int-abs-is-common-divisor-ℤ :
  {x y d : ℤ} →
  is-common-divisor-ℤ x y d → is-common-divisor-ℤ x y (int-abs-ℤ d)
is-common-divisor-int-abs-is-common-divisor-ℤ =
  map-prod div-int-abs-div-ℤ div-int-abs-div-ℤ

is-common-divisor-is-common-divisor-int-abs-ℤ :
  {x y d : ℤ} →
  is-common-divisor-ℤ x y (int-abs-ℤ d) → is-common-divisor-ℤ x y d
is-common-divisor-is-common-divisor-int-abs-ℤ =
  map-prod div-div-int-abs-ℤ div-div-int-abs-ℤ

is-gcd-int-is-gcd-ℕ :
  {x y d : ℕ} → is-gcd-ℕ x y d → is-gcd-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d)
pr1 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) = is-nonnegative-int-ℕ d
pr1 (pr2 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) k) =
  ( ( ( ( div-div-int-abs-ℤ) ∘
        ( div-int-div-ℕ)) ∘
      ( pr1 (H (abs-ℤ k)))) ∘
    ( is-common-divisor-is-common-divisor-int-ℕ)) ∘
  ( is-common-divisor-int-abs-is-common-divisor-ℤ)
pr2 (pr2 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) k) =
  ( ( ( ( is-common-divisor-is-common-divisor-int-abs-ℤ) ∘
        ( is-common-divisor-int-is-common-divisor-ℕ)) ∘
      ( pr2 (H (abs-ℤ k)))) ∘
    ( div-div-int-ℕ)) ∘
  ( div-int-abs-div-ℤ)

is-gcd-is-gcd-int-ℕ :
  {x y d : ℕ} → is-gcd-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d) → is-gcd-ℕ x y d
pr1 (is-gcd-is-gcd-int-ℕ {x} {y} {d} H k) =
  ( ( div-div-int-ℕ) ∘
    ( pr1 (pr2 H (int-ℕ k)))) ∘
  ( is-common-divisor-int-is-common-divisor-ℕ)
pr2 (is-gcd-is-gcd-int-ℕ {x} {y} {d} H k) =
  ( ( is-common-divisor-is-common-divisor-int-ℕ) ∘
    ( pr2 (pr2 H (int-ℕ k)))) ∘
  ( div-int-div-ℕ)

nat-gcd-ℤ : ℤ → ℤ → ℕ
nat-gcd-ℤ x y = gcd-ℕ (abs-ℤ x) (abs-ℤ y)

gcd-ℤ : ℤ → ℤ → ℤ
gcd-ℤ x y = int-ℕ (nat-gcd-ℤ x y)

is-nonnegative-gcd-ℤ : (x y : ℤ) → is-nonnegative-ℤ (gcd-ℤ x y)
is-nonnegative-gcd-ℤ x y = is-nonnegative-int-ℕ (nat-gcd-ℤ x y)

gcd-nonnegative-ℤ : ℤ → ℤ → nonnegative-ℤ
pr1 (gcd-nonnegative-ℤ x y) = gcd-ℤ x y
pr2 (gcd-nonnegative-ℤ x y) = is-nonnegative-gcd-ℤ x y

is-gcd-gcd-ℤ : (x y : ℤ) → is-gcd-ℤ x y (gcd-ℤ x y)
pr1 (is-gcd-gcd-ℤ x y) = is-nonnegative-gcd-ℤ x y
pr1 (pr2 (is-gcd-gcd-ℤ x y) k) =
  ( ( ( ( ( div-sim-unit-ℤ
            ( sim-unit-abs-ℤ k)
            ( refl-sim-unit-ℤ (gcd-ℤ x y))) ∘
          ( div-int-div-ℕ)) ∘
        ( pr1 (is-gcd-gcd-ℕ (abs-ℤ x) (abs-ℤ y) (abs-ℤ k)))) ∘
      ( is-common-divisor-is-common-divisor-int-ℕ)) ∘
    ( is-common-divisor-int-abs-is-common-divisor-ℤ)) ∘
  ( is-common-divisor-sim-unit-ℤ
    ( symm-sim-unit-ℤ (sim-unit-abs-ℤ x))
    ( symm-sim-unit-ℤ (sim-unit-abs-ℤ y))
    ( refl-sim-unit-ℤ k))
pr2 (pr2 (is-gcd-gcd-ℤ x y) k) =
  ( ( ( ( ( is-common-divisor-sim-unit-ℤ
            ( sim-unit-abs-ℤ x)
            ( sim-unit-abs-ℤ y)
            ( refl-sim-unit-ℤ k)) ∘
          ( is-common-divisor-is-common-divisor-int-abs-ℤ)) ∘
        ( is-common-divisor-int-is-common-divisor-ℕ)) ∘
      ( pr2 (is-gcd-gcd-ℕ (abs-ℤ x) (abs-ℤ y) (abs-ℤ k)))) ∘
    ( div-div-int-ℕ)) ∘
  ( div-sim-unit-ℤ
    ( symm-sim-unit-ℤ (sim-unit-abs-ℤ k))
    ( refl-sim-unit-ℤ (gcd-ℤ x y)))

is-common-divisor-gcd-ℤ :
  (x y : ℤ) → is-common-divisor-ℤ x y (gcd-ℤ x y)
is-common-divisor-gcd-ℤ x y =
  pr2 (pr2 (is-gcd-gcd-ℤ x y) (gcd-ℤ x y)) (refl-div-ℤ (gcd-ℤ x y))

div-gcd-is-common-divisor-ℤ :
  (x y k : ℤ) → is-common-divisor-ℤ x y k → div-ℤ k (gcd-ℤ x y)
div-gcd-is-common-divisor-ℤ x y k H =
  pr1 (pr2 (is-gcd-gcd-ℤ x y) k) H

is-positive-gcd-is-positive-left-ℤ :
  (x y : ℤ) → is-positive-ℤ x → is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-is-positive-left-ℤ x y H =
  is-positive-int-ℕ
    ( gcd-ℕ (abs-ℤ x) (abs-ℤ y))
    ( is-nonzero-gcd-ℕ
      ( abs-ℤ x)
      ( abs-ℤ y)
      ( λ p → is-nonzero-abs-ℤ x H (f p)))
  where
  f : is-zero-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y)) → is-zero-ℕ (abs-ℤ x)
  f = is-zero-left-is-zero-add-ℕ (abs-ℤ x) (abs-ℤ y)

is-positive-gcd-is-positive-right-ℤ :
  (x y : ℤ) → is-positive-ℤ y → is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-is-positive-right-ℤ x y H =
  is-positive-int-ℕ
    ( gcd-ℕ (abs-ℤ x) (abs-ℤ y))
    ( is-nonzero-gcd-ℕ
      ( abs-ℤ x)
      ( abs-ℤ y)
      ( λ p → is-nonzero-abs-ℤ y H (f p)))
  where
  f : is-zero-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y)) → is-zero-ℕ (abs-ℤ y)
  f = is-zero-right-is-zero-add-ℕ (abs-ℤ x) (abs-ℤ y)

is-positive-gcd-ℤ :
  (x y : ℤ) → coprod (is-positive-ℤ x) (is-positive-ℤ y) →
  is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-ℤ x y (inl H) = is-positive-gcd-is-positive-left-ℤ x y H
is-positive-gcd-ℤ x y (inr H) = is-positive-gcd-is-positive-right-ℤ x y H

is-commutative-gcd-ℤ :
  (x y : ℤ) → Id (gcd-ℤ x y) (gcd-ℤ y x)
is-commutative-gcd-ℤ x y =
  ap int-ℕ (is-commutative-gcd-ℕ (abs-ℤ x) (abs-ℤ y)) 
```
