---
title: Univalent Mathematics in Agda
---

# Divisibility of integers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.divisibility-integers where

open import elementary-number-theory.absolute-value-integers using
  ( abs-ℤ; int-abs-ℤ)
open import elementary-number-theory.addition-integers using (add-ℤ; ap-add-ℤ)
open import foundation.cartesian-product-types using (_×_)
open import foundations.coproduct-types using (coprod; inl; inr)
open import foundations.decidable-types using
  ( is-decidable; dn-elim-is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import elementary-number-theory.divisibility-natural-numbers using
  ( div-ℕ; div-eq-ℕ)
open import foundations.empty-type using (ex-falso)
open import elementary-number-theory.equality-integers using
  ( Eq-eq-ℤ; has-decidable-equality-ℤ; is-decidable-is-zero-ℤ)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap; tr)
open import elementary-number-theory.integers using
  ( ℤ; zero-ℤ; one-ℤ; is-zero-ℤ; neg-ℤ; int-ℕ; is-nonnegative-ℤ; is-one-ℤ;
    is-injective-int-ℕ; is-nonnegative-eq-ℤ; is-nonnegative-int-ℕ; is-neg-one-ℤ;
    neg-one-ℤ; is-nonzero-ℤ; neg-neg-ℤ)
open import foundation.levels using (UU; lzero)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; mul-ℤ'; left-unit-law-mul-ℤ; associative-mul-ℤ; right-unit-law-mul-ℤ;
    left-zero-law-mul-ℤ; right-zero-law-mul-ℤ; right-distributive-mul-add-ℤ;
    left-negative-law-mul-ℤ; mul-int-ℕ; is-nonnegative-left-factor-mul-ℤ;
    compute-mul-ℤ; commutative-mul-ℤ; is-injective-mul-ℤ'; is-injective-mul-ℤ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-one-ℕ)
open import foundations.negation using (¬)
open import foundations.unit-type using (star)
```

# Divisibility of integers

```agda
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

abstract
  is-one-is-unit-int-ℕ : (x : ℕ) → is-unit-ℤ (int-ℕ x) → is-one-ℕ x
  is-one-is-unit-int-ℕ x H with is-one-or-neg-one-is-unit-ℤ (int-ℕ x) H
  ... | inl p = is-injective-int-ℕ p
  ... | inr p = ex-falso (tr is-nonnegative-ℤ p (is-nonnegative-int-ℕ x))

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
```
