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
        ( inv (linear-diff-ℤ y z x) ∙ is-zero-diff-ℤ p)))

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
  is-nonnegative-eq-ℤ (inv (right-translation-diff-ℤ {x} {y} {z}))

preserves-order-add-ℤ :
  {x y : ℤ} (z : ℤ) → leq-ℤ x y → leq-ℤ (add-ℤ z x) (add-ℤ z y)
preserves-order-add-ℤ {x} {y} z =
  is-nonnegative-eq-ℤ (inv (left-translation-diff-ℤ {x} {y} {z}))

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
  is-nonnegative-eq-ℤ (right-translation-diff-ℤ {x} {y} {z})

reflects-order-add-ℤ :
  {x y z : ℤ} → leq-ℤ (add-ℤ z x) (add-ℤ z y) → leq-ℤ x y
reflects-order-add-ℤ {x} {y} {z} =
  is-nonnegative-eq-ℤ (left-translation-diff-ℤ {x} {y} {z})

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
refl-div-ℤ x = pair one-ℤ (left-unit-law-mul-ℤ x)

trans-div-ℤ :
  (x y z : ℤ) → div-ℤ x y → div-ℤ y z → div-ℤ x z
trans-div-ℤ x y z (pair d p) (pair e q) =
  pair
    ( mul-ℤ e d)
    ( ( associative-mul-ℤ e d x) ∙
      ( ( ap (mul-ℤ e) p) ∙
        ( q)))

-- Basic properties of divisibility

div-one-ℤ : (x : ℤ) → div-ℤ one-ℤ x
div-one-ℤ x = pair x (right-unit-law-mul-ℤ x)

div-zero-ℤ : (x : ℤ) → div-ℤ x zero-ℤ
div-zero-ℤ x = pair zero-ℤ (left-zero-law-mul-ℤ x)

is-zero-div-zero-ℤ :
  (x : ℤ) → div-ℤ zero-ℤ x → is-zero-ℤ x
is-zero-div-zero-ℤ x (pair d p) = inv p ∙ right-zero-law-mul-ℤ d

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
div-is-unit-ℤ x y (pair d p) =
  pair
    ( mul-ℤ y d)
    ( associative-mul-ℤ y d x ∙ (ap (mul-ℤ y) p ∙ right-unit-law-mul-ℤ y))

-- An integer is a unit if and only if it is 1 or -1.

is-one-or-neg-one-ℤ : ℤ → UU lzero
is-one-or-neg-one-ℤ x = coprod (is-one-ℤ x) (is-neg-one-ℤ x)

is-unit-one-ℤ : is-unit-ℤ one-ℤ
is-unit-one-ℤ = refl-div-ℤ one-ℤ

one-unit-ℤ : unit-ℤ
one-unit-ℤ = pair one-ℤ is-unit-one-ℤ

is-unit-is-one-ℤ :
  (x : ℤ) → is-one-ℤ x → is-unit-ℤ x
is-unit-is-one-ℤ .one-ℤ refl = is-unit-one-ℤ

is-unit-neg-one-ℤ : is-unit-ℤ neg-one-ℤ
is-unit-neg-one-ℤ = pair neg-one-ℤ refl

neg-one-unit-ℤ : unit-ℤ
neg-one-unit-ℤ = pair neg-one-ℤ is-unit-neg-one-ℤ

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
is-unit-mul-ℤ x y (pair d p) (pair e q) =
  pair
    ( mul-ℤ e d)
    ( ( associative-mul-ℤ e d (mul-ℤ x y)) ∙
      ( ( ap
          ( mul-ℤ e)
          ( ( inv (associative-mul-ℤ d x y)) ∙
            ( ap (mul-ℤ' y) p))) ∙
        ( q)))

mul-unit-ℤ : unit-ℤ → unit-ℤ → unit-ℤ
mul-unit-ℤ (pair x H) (pair y K) = pair (mul-ℤ x y) (is-unit-mul-ℤ x y H K)

is-unit-left-factor-mul-ℤ :
  (x y : ℤ) → is-unit-ℤ (mul-ℤ x y) → is-unit-ℤ x
is-unit-left-factor-mul-ℤ x y (pair d p) =
  pair
    ( mul-ℤ d y)
    ( associative-mul-ℤ d y x ∙ (ap (mul-ℤ d) (commutative-mul-ℤ y x) ∙ p))

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
presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inl star)} H =
  pair one-unit-ℤ refl
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
refl-presim-unit-ℤ x = pair one-unit-ℤ (left-unit-law-mul-ℤ x)

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
  f (inl refl) = pair one-unit-ℤ (inv p)
  f (inr refl) =
    pair neg-one-unit-ℤ (inv (inv (neg-neg-ℤ x) ∙ ap (mul-ℤ neg-one-ℤ) p))

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
  f (inl refl) (inl refl) = pair one-unit-ℤ (p ∙ q)
  f (inl refl) (inr refl) = pair neg-one-unit-ℤ (ap neg-ℤ p ∙ q)
  f (inr refl) (inl refl) = pair neg-one-unit-ℤ (p ∙ q)
  f (inr refl) (inr refl) =
    pair one-unit-ℤ (inv (neg-neg-ℤ x) ∙ (ap neg-ℤ p ∙ q))

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
  f (inr g) =
    pair
      ( pair d
        ( pair e
          ( is-injective-mul-ℤ x g
            ( ( commutative-mul-ℤ x (mul-ℤ e d)) ∙
              ( ( associative-mul-ℤ e d x) ∙
                ( ( ap (mul-ℤ e) p) ∙
                  ( q ∙ inv (right-unit-law-mul-ℤ x))))))))
      ( p)

-- We show that sim-unit-ℤ |x| x holds

sim-unit-abs-ℤ : (x : ℤ) → sim-unit-ℤ (int-abs-ℤ x) x
sim-unit-abs-ℤ (inl x) f = pair neg-one-unit-ℤ refl
sim-unit-abs-ℤ (inr (inl star)) = refl-sim-unit-ℤ zero-ℤ
sim-unit-abs-ℤ (inr (inr x)) = refl-sim-unit-ℤ (inr (inr x))

-- We introduce the condition on ℤ of being a gcd.

is-common-divisor-ℤ : ℤ → ℤ → ℤ → UU lzero
is-common-divisor-ℤ x y d = (div-ℤ d x) × (div-ℤ d y)

is-gcd-ℤ : ℤ → ℤ → ℤ → UU lzero
is-gcd-ℤ x y d =
  is-nonnegative-ℤ d × ((k : ℤ) → is-common-divisor-ℤ x y k ↔ div-ℤ k d)

-- We relate divisibility and being a gcd on ℕ and on ℤ

div-int-div-ℕ :
  {x y : ℕ} → div-ℕ x y → div-ℤ (int-ℕ x) (int-ℕ y)
div-int-div-ℕ {x} {y} (pair d p) =
  pair (int-ℕ d) (mul-int-ℕ d x ∙ ap int-ℕ p)

int-abs-is-nonnegative-ℤ :
  (x : ℤ) → is-nonnegative-ℤ x → Id (int-abs-ℤ x) x
int-abs-is-nonnegative-ℤ (inr (inl star)) star = refl
int-abs-is-nonnegative-ℤ (inr (inr x)) star = refl

div-div-int-ℕ :
  {x y : ℕ} → div-ℤ (int-ℕ x) (int-ℕ y) → div-ℕ x y
div-div-int-ℕ {zero-ℕ} {y} (pair d p) =
  div-eq-ℕ zero-ℕ y
    ( inv (is-injective-int-ℕ (is-zero-div-zero-ℤ (int-ℕ y) (pair d p))))
div-div-int-ℕ {succ-ℕ x} {y} (pair d p) =
  pair
    ( abs-ℤ d)
    ( is-injective-int-ℕ
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
          ( p))))

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

div-presim-unit-ℤ :
  {x y x' y' : ℤ} → presim-unit-ℤ x x' → presim-unit-ℤ y y' →
  div-ℤ x y → div-ℤ x' y'
div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p) =
  pair
    ( mul-ℤ (mul-ℤ (int-unit-ℤ v) d) (int-unit-ℤ u))
    ( ( ap (mul-ℤ (mul-ℤ (mul-ℤ (int-unit-ℤ v) d) (int-unit-ℤ u))) (inv q)) ∙
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
              ( r))))))

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

is-common-divisor-sim-unit-ℤ :
  {x x' y y' d d' : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' → sim-unit-ℤ d d' →
  is-common-divisor-ℤ x y d → is-common-divisor-ℤ x' y' d'
is-common-divisor-sim-unit-ℤ H K L =
  map-prod (div-sim-unit-ℤ L H) (div-sim-unit-ℤ L K)

is-gcd-sim-unit-ℤ :
  {x x' y y' d : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' →
  is-gcd-ℤ x y d → is-gcd-ℤ x' y' d
is-gcd-sim-unit-ℤ H K =
  map-prod id
    ( λ G k →
      pair
        ( ( pr1 (G k)) ∘
          ( is-common-divisor-sim-unit-ℤ
            ( symm-sim-unit-ℤ H)
            ( symm-sim-unit-ℤ K)
            ( refl-sim-unit-ℤ k)))
        ( ( is-common-divisor-sim-unit-ℤ H K (refl-sim-unit-ℤ k)) ∘
          ( pr2 (G k))))

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
is-gcd-int-is-gcd-ℕ {x} {y} {d} H =
  pair
    ( is-nonnegative-int-ℕ d)
    ( λ k →
      pair
        ( ( ( ( ( div-div-int-abs-ℤ) ∘
                ( div-int-div-ℕ)) ∘
              ( pr1 (H (abs-ℤ k)))) ∘
            ( is-common-divisor-is-common-divisor-int-ℕ)) ∘
          ( is-common-divisor-int-abs-is-common-divisor-ℤ))
        ( ( ( ( ( is-common-divisor-is-common-divisor-int-abs-ℤ) ∘
                ( is-common-divisor-int-is-common-divisor-ℕ)) ∘
              ( pr2 (H (abs-ℤ k)))) ∘
            ( div-div-int-ℕ)) ∘
          ( div-int-abs-div-ℤ)))

is-gcd-is-gcd-int-ℕ :
  {x y d : ℕ} → is-gcd-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d) → is-gcd-ℕ x y d
is-gcd-is-gcd-int-ℕ {x} {y} {d} H k =
  pair
    ( ( ( div-div-int-ℕ) ∘
        ( pr1 (pr2 H (int-ℕ k)))) ∘
      ( is-common-divisor-int-is-common-divisor-ℕ))
    ( ( ( is-common-divisor-is-common-divisor-int-ℕ) ∘
        ( pr2 (pr2 H (int-ℕ k)))) ∘
      ( div-int-div-ℕ))

nat-gcd-ℤ : ℤ → ℤ → ℕ
nat-gcd-ℤ x y = gcd-ℕ (abs-ℤ x) (abs-ℤ y)

gcd-ℤ : ℤ → ℤ → ℤ
gcd-ℤ x y = int-ℕ (nat-gcd-ℤ x y)

is-nonnegative-gcd-ℤ : (x y : ℤ) → is-nonnegative-ℤ (gcd-ℤ x y)
is-nonnegative-gcd-ℤ x y = is-nonnegative-int-ℕ (nat-gcd-ℤ x y)

gcd-nonnegative-ℤ : ℤ → ℤ → nonnegative-ℤ
gcd-nonnegative-ℤ x y = pair (gcd-ℤ x y) (is-nonnegative-gcd-ℤ x y)

is-gcd-gcd-ℤ : (x y : ℤ) → is-gcd-ℤ x y (gcd-ℤ x y)
is-gcd-gcd-ℤ x y =
  pair
    ( is-nonnegative-gcd-ℤ x y)
    ( λ k →
      pair
        ( ( ( ( ( ( div-sim-unit-ℤ
                    ( sim-unit-abs-ℤ k)
                    ( refl-sim-unit-ℤ (gcd-ℤ x y))) ∘
                  ( div-int-div-ℕ)) ∘
                ( pr1 (is-gcd-gcd-ℕ (abs-ℤ x) (abs-ℤ y) (abs-ℤ k)))) ∘
              ( is-common-divisor-is-common-divisor-int-ℕ)) ∘
            ( is-common-divisor-int-abs-is-common-divisor-ℤ)) ∘
          ( is-common-divisor-sim-unit-ℤ
            ( symm-sim-unit-ℤ (sim-unit-abs-ℤ x))
            ( symm-sim-unit-ℤ (sim-unit-abs-ℤ y))
            ( refl-sim-unit-ℤ k)))
        ( ( ( ( ( ( is-common-divisor-sim-unit-ℤ
                    ( sim-unit-abs-ℤ x)
                    ( sim-unit-abs-ℤ y)
                    ( refl-sim-unit-ℤ k)) ∘
                  ( is-common-divisor-is-common-divisor-int-abs-ℤ)) ∘
                ( is-common-divisor-int-is-common-divisor-ℕ)) ∘
              ( pr2 (is-gcd-gcd-ℕ (abs-ℤ x) (abs-ℤ y) (abs-ℤ k)))) ∘
            ( div-div-int-ℕ)) ∘
          ( div-sim-unit-ℤ
            ( symm-sim-unit-ℤ (sim-unit-abs-ℤ k))
            ( refl-sim-unit-ℤ (gcd-ℤ x y)))))

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
