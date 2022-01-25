---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.greatest-common-divisor-natural-numbers where

open import foundations.addition-natural-numbers using
  ( add-ℕ; is-zero-left-is-zero-add-ℕ; is-zero-right-is-zero-add-ℕ)
open import foundations.cartesian-product-types using (_×_)
open import foundations.coproduct-types using (inl; inr)
open import foundations.decidable-types using
  ( is-decidable-fam; is-decidable-prod; is-decidable-function-type';
    is-decidable-neg; dn-elim-is-decidable)
open import foundations.dependent-pair-types using (pair; pr1; pr2)
open import foundations.distance-natural-numbers using
  ( dist-ℕ; right-unit-law-dist-ℕ)
open import foundations.divisibility-natural-numbers using
  ( div-ℕ; refl-div-ℕ; antisymmetric-div-ℕ; concatenate-div-eq-ℕ; div-add-ℕ;
    div-zero-ℕ; transitive-div-ℕ; div-right-summand-ℕ; div-mul-ℕ;
    leq-div-succ-ℕ; preserves-div-mul-ℕ; reflects-div-mul-ℕ)
open import foundations.empty-type using (ex-falso)
open import foundations.equality-natural-numbers using (is-decidable-is-zero-ℕ)
open import foundations.euclidean-division-natural-numbers using
  ( remainder-euclidean-division-ℕ; quotient-euclidean-division-ℕ;
    eq-quotient-euclidean-division-ℕ; eq-euclidean-division-ℕ;
    strict-upper-bound-remainder-euclidean-division-ℕ)
open import foundations.functoriality-cartesian-product-types using (map-prod)
open import foundations.identity-types using (Id; refl; _∙_; inv; ap)
open import foundations.inequality-natural-numbers using
  ( leq-ℕ; concatenate-leq-eq-ℕ; leq-mul-ℕ'; is-zero-leq-zero-ℕ; le-ℕ;
    contradiction-le-ℕ)
open import foundations.levels using (UU; lzero)
open import foundations.logical-equivalence using (_↔_)
open import foundations.multiplication-natural-numbers using (mul-ℕ)
open import foundations.modular-arithmetic-standard-finite-types using
  ( is-decidable-div-ℕ)
open import foundations.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-nonzero-ℕ; is-successor-ℕ; is-successor-is-nonzero-ℕ;
    is-zero-ℕ)
open import foundations.well-ordering-principle-natural-numbers using
  ( is-decidable-bounded-Π-ℕ; minimal-element-ℕ; well-ordering-principle-ℕ;
    is-lower-bound-ℕ)
```

# The greatest common divisor of two natural numbers

```agda
is-common-divisor-ℕ : (a b x : ℕ) → UU lzero
is-common-divisor-ℕ a b x = (div-ℕ x a) × (div-ℕ x b)

refl-is-common-divisor-ℕ :
  (x : ℕ) → is-common-divisor-ℕ x x x
pr1 (refl-is-common-divisor-ℕ x) = refl-div-ℕ x
pr2 (refl-is-common-divisor-ℕ x) = refl-div-ℕ x

is-decidable-is-common-divisor-ℕ :
  (a b : ℕ) → is-decidable-fam (is-common-divisor-ℕ a b)
is-decidable-is-common-divisor-ℕ a b x =
  is-decidable-prod
    ( is-decidable-div-ℕ x a)
    ( is-decidable-div-ℕ x b)

is-gcd-ℕ : (a b d : ℕ) → UU lzero
is-gcd-ℕ a b d = (x : ℕ) → (is-common-divisor-ℕ a b x) ↔ (div-ℕ x d)

is-common-divisor-is-gcd-ℕ :
  (a b d : ℕ) → is-gcd-ℕ a b d → is-common-divisor-ℕ a b d
is-common-divisor-is-gcd-ℕ a b d H = pr2 (H d) (refl-div-ℕ d)

{- Proposition 8.4.2 -}

uniqueness-is-gcd-ℕ :
  (a b d d' : ℕ) → is-gcd-ℕ a b d → is-gcd-ℕ a b d' → Id d d'
uniqueness-is-gcd-ℕ a b d d' H H' =
  antisymmetric-div-ℕ d d'
    ( pr1 (H' d) (is-common-divisor-is-gcd-ℕ a b d H))
    ( pr1 (H d') (is-common-divisor-is-gcd-ℕ a b d' H'))

{- Definition 8.4.3 -}

is-multiple-of-gcd-ℕ : (a b n : ℕ) → UU lzero
is-multiple-of-gcd-ℕ a b n =
  is-nonzero-ℕ (add-ℕ a b) →
  (is-nonzero-ℕ n) × ((x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x n)

{- Proposition 8.4.4 -}

leq-sum-is-common-divisor-ℕ' :
  (a b d : ℕ) →
  is-successor-ℕ (add-ℕ a b) → is-common-divisor-ℕ a b d → leq-ℕ d (add-ℕ a b)
leq-sum-is-common-divisor-ℕ' a zero-ℕ d (pair k p) H =
  concatenate-leq-eq-ℕ d
    ( leq-div-succ-ℕ d k (concatenate-div-eq-ℕ (pr1 H) p))
    ( inv p)
leq-sum-is-common-divisor-ℕ' a (succ-ℕ b) d (pair k p) H =
  leq-div-succ-ℕ d (add-ℕ a b) (div-add-ℕ d a (succ-ℕ b) (pr1 H) (pr2 H))

leq-sum-is-common-divisor-ℕ :
  (a b d : ℕ) →
  is-nonzero-ℕ (add-ℕ a b) → is-common-divisor-ℕ a b d → leq-ℕ d (add-ℕ a b)
leq-sum-is-common-divisor-ℕ a b d H =
  leq-sum-is-common-divisor-ℕ' a b d (is-successor-is-nonzero-ℕ H)

is-decidable-is-multiple-of-gcd-ℕ :
  (a b : ℕ) → is-decidable-fam (is-multiple-of-gcd-ℕ a b)
is-decidable-is-multiple-of-gcd-ℕ a b n =
  is-decidable-function-type'
    ( is-decidable-neg (is-decidable-is-zero-ℕ (add-ℕ a b)))
    ( λ np →
      is-decidable-prod
        ( is-decidable-neg (is-decidable-is-zero-ℕ n))
        ( is-decidable-bounded-Π-ℕ
          ( is-common-divisor-ℕ a b)
          ( λ x → div-ℕ x n)
          ( is-decidable-is-common-divisor-ℕ a b)
          ( λ x → is-decidable-div-ℕ x n)
          ( add-ℕ a b)
          ( λ x → leq-sum-is-common-divisor-ℕ a b x np)))

{- Lemma 8.4.5 -}

sum-is-multiple-of-gcd-ℕ : (a b : ℕ) → is-multiple-of-gcd-ℕ a b (add-ℕ a b)
pr1 (sum-is-multiple-of-gcd-ℕ a b np) = np
pr2 (sum-is-multiple-of-gcd-ℕ a b np) x H = div-add-ℕ x a b (pr1 H) (pr2 H)

{- Definition 8.4.6 The greatest common divisor -}

abstract
  GCD-ℕ : (a b : ℕ) → minimal-element-ℕ (is-multiple-of-gcd-ℕ a b)
  GCD-ℕ a b =
    well-ordering-principle-ℕ
      ( is-multiple-of-gcd-ℕ a b)
      ( is-decidable-is-multiple-of-gcd-ℕ a b)
      ( pair (add-ℕ a b) (sum-is-multiple-of-gcd-ℕ a b))

gcd-ℕ : ℕ → ℕ → ℕ
gcd-ℕ a b = pr1 (GCD-ℕ a b)

is-multiple-of-gcd-gcd-ℕ : (a b : ℕ) → is-multiple-of-gcd-ℕ a b (gcd-ℕ a b)
is-multiple-of-gcd-gcd-ℕ a b = pr1 (pr2 (GCD-ℕ a b))

is-lower-bound-gcd-ℕ :
  (a b : ℕ) → is-lower-bound-ℕ (is-multiple-of-gcd-ℕ a b) (gcd-ℕ a b)
is-lower-bound-gcd-ℕ a b = pr2 (pr2 (GCD-ℕ a b))

{- Lemma 8.4.7 -}

is-zero-gcd-ℕ :
  (a b : ℕ) → is-zero-ℕ (add-ℕ a b) → is-zero-ℕ (gcd-ℕ a b)
is-zero-gcd-ℕ a b p =
  is-zero-leq-zero-ℕ
    ( gcd-ℕ a b)
    ( concatenate-leq-eq-ℕ
      ( gcd-ℕ a b)
      ( is-lower-bound-gcd-ℕ a b
        ( add-ℕ a b)
        ( sum-is-multiple-of-gcd-ℕ a b))
      ( p))

is-zero-gcd-zero-zero-ℕ : is-zero-ℕ (gcd-ℕ zero-ℕ zero-ℕ)
is-zero-gcd-zero-zero-ℕ = is-zero-gcd-ℕ zero-ℕ zero-ℕ refl

is-zero-add-is-zero-gcd-ℕ :
  (a b : ℕ) → is-zero-ℕ (gcd-ℕ a b) → is-zero-ℕ (add-ℕ a b)
is-zero-add-is-zero-gcd-ℕ a b H =
  dn-elim-is-decidable
    ( is-zero-ℕ (add-ℕ a b))
    ( is-decidable-is-zero-ℕ (add-ℕ a b))
    ( λ f → pr1 (is-multiple-of-gcd-gcd-ℕ a b f) H)

is-nonzero-gcd-ℕ :
  (a b : ℕ) → is-nonzero-ℕ (add-ℕ a b) → is-nonzero-ℕ (gcd-ℕ a b)
is-nonzero-gcd-ℕ a b ne = pr1 (is-multiple-of-gcd-gcd-ℕ a b ne)

is-successor-gcd-ℕ :
  (a b : ℕ) → is-nonzero-ℕ (add-ℕ a b) → is-successor-ℕ (gcd-ℕ a b)
is-successor-gcd-ℕ a b ne =
  is-successor-is-nonzero-ℕ (is-nonzero-gcd-ℕ a b ne)

{- Theorem 8.4.8 -}

-- any common divisor is also a divisor of the gcd
div-gcd-is-common-divisor-ℕ :
  (a b x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x (gcd-ℕ a b)
div-gcd-is-common-divisor-ℕ a b x H with
  is-decidable-is-zero-ℕ (add-ℕ a b)
... | inl p = concatenate-div-eq-ℕ (div-zero-ℕ x) (inv (is-zero-gcd-ℕ a b p))
... | inr np = pr2 (is-multiple-of-gcd-gcd-ℕ a b np) x H

-- if every common divisor divides a number r < gcd a b, then r = 0.
is-zero-is-common-divisor-le-gcd-ℕ :
  (a b r : ℕ) → le-ℕ r (gcd-ℕ a b) →
  ((x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x r) → is-zero-ℕ r
is-zero-is-common-divisor-le-gcd-ℕ a b r l d with is-decidable-is-zero-ℕ r
... | inl H = H
... | inr x =
  ex-falso
    ( contradiction-le-ℕ r (gcd-ℕ a b) l
      ( is-lower-bound-gcd-ℕ a b r (λ np → pair x d)))

-- any divisor of gcd a b also divides a
is-divisor-left-div-gcd-ℕ :
  (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → div-ℕ x a
is-divisor-left-div-gcd-ℕ a b x d with
  is-decidable-is-zero-ℕ (add-ℕ a b)
... | inl p =
  concatenate-div-eq-ℕ (div-zero-ℕ x) (inv (is-zero-left-is-zero-add-ℕ a b p))
... | inr np =
  transitive-div-ℕ x (gcd-ℕ a b) a d
    ( pair q
      ( ( ( α) ∙
          ( ap ( dist-ℕ a)
               ( is-zero-is-common-divisor-le-gcd-ℕ a b r B
                 ( λ x H →
                   div-right-summand-ℕ x (mul-ℕ q (gcd-ℕ a b)) r
                     ( div-mul-ℕ q x (gcd-ℕ a b)
                       ( div-gcd-is-common-divisor-ℕ a b x H))
                     ( concatenate-div-eq-ℕ (pr1 H) (inv β)))))) ∙
        ( right-unit-law-dist-ℕ a)))
  where
  r = remainder-euclidean-division-ℕ (gcd-ℕ a b) a
  q = quotient-euclidean-division-ℕ (gcd-ℕ a b) a
  α = eq-quotient-euclidean-division-ℕ (gcd-ℕ a b) a
  B = strict-upper-bound-remainder-euclidean-division-ℕ (gcd-ℕ a b) a
       ( is-nonzero-gcd-ℕ a b np)
  β = eq-euclidean-division-ℕ (gcd-ℕ a b) a

-- any divisor of gcd a b also divides b
is-divisor-right-div-gcd-ℕ :
  (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → div-ℕ x b
is-divisor-right-div-gcd-ℕ a b x d with
  is-decidable-is-zero-ℕ (add-ℕ a b)
... | inl p =
  concatenate-div-eq-ℕ (div-zero-ℕ x) (inv (is-zero-right-is-zero-add-ℕ a b p))
... | inr np =
  transitive-div-ℕ x (gcd-ℕ a b) b d
    ( pair q
      ( ( α ∙ ( ap ( dist-ℕ b)
               ( is-zero-is-common-divisor-le-gcd-ℕ a b r B
                 ( λ x H →
                   div-right-summand-ℕ x (mul-ℕ q (gcd-ℕ a b)) r
                     ( div-mul-ℕ q x (gcd-ℕ a b)
                       ( div-gcd-is-common-divisor-ℕ a b x H))
                     ( concatenate-div-eq-ℕ (pr2 H) (inv β)))))) ∙
        ( right-unit-law-dist-ℕ b)))
  where
  r = remainder-euclidean-division-ℕ (gcd-ℕ a b) b
  q = quotient-euclidean-division-ℕ (gcd-ℕ a b) b
  α = eq-quotient-euclidean-division-ℕ (gcd-ℕ a b) b
  B = strict-upper-bound-remainder-euclidean-division-ℕ (gcd-ℕ a b) b
       ( is-nonzero-gcd-ℕ a b np)
  β = eq-euclidean-division-ℕ (gcd-ℕ a b) b

-- any divisor of gcd a b is a common divisor
is-common-divisor-div-gcd-ℕ :
  (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → is-common-divisor-ℕ a b x
pr1 (is-common-divisor-div-gcd-ℕ a b x d) = is-divisor-left-div-gcd-ℕ a b x d
pr2 (is-common-divisor-div-gcd-ℕ a b x d) = is-divisor-right-div-gcd-ℕ a b x d

-- gcd a b is itself a common divisor
is-common-divisor-gcd-ℕ : (a b : ℕ) → is-common-divisor-ℕ a b (gcd-ℕ a b)
is-common-divisor-gcd-ℕ a b =
  is-common-divisor-div-gcd-ℕ a b (gcd-ℕ a b) (refl-div-ℕ (gcd-ℕ a b))

-- gcd a b is the greatest common divisor
is-gcd-gcd-ℕ : (a b : ℕ) → is-gcd-ℕ a b (gcd-ℕ a b)
pr1 (is-gcd-gcd-ℕ a b x) = div-gcd-is-common-divisor-ℕ a b x
pr2 (is-gcd-gcd-ℕ a b x) = is-common-divisor-div-gcd-ℕ a b x

-- We show that gcd-ℕ is commutative

is-commutative-gcd-ℕ : (a b : ℕ) → Id (gcd-ℕ a b) (gcd-ℕ b a)
is-commutative-gcd-ℕ a b =
  antisymmetric-div-ℕ
    ( gcd-ℕ a b)
    ( gcd-ℕ b a)
    ( pr1 (is-gcd-gcd-ℕ b a (gcd-ℕ a b)) (σ (is-common-divisor-gcd-ℕ a b)))
    ( pr1 (is-gcd-gcd-ℕ a b (gcd-ℕ b a)) (σ (is-common-divisor-gcd-ℕ b a)))
  where
  σ : {A B : UU lzero} → A × B → B × A
  pr1 (σ (pair x y)) = y
  pr2 (σ (pair x y)) = x
```

```agda
preserves-is-common-divisor-mul-ℕ :
  (k a b d : ℕ) → is-common-divisor-ℕ a b d →
  is-common-divisor-ℕ (mul-ℕ k a) (mul-ℕ k b) (mul-ℕ k d)
preserves-is-common-divisor-mul-ℕ k a b d =
  map-prod
    ( preserves-div-mul-ℕ k d a)
    ( preserves-div-mul-ℕ k d b)

reflects-is-common-divisor-mul-ℕ :
  (k a b d : ℕ) → is-nonzero-ℕ k →
  is-common-divisor-ℕ (mul-ℕ k a) (mul-ℕ k b) (mul-ℕ k d) →
  is-common-divisor-ℕ a b d
reflects-is-common-divisor-mul-ℕ k a b d H =
  map-prod
    ( reflects-div-mul-ℕ k d a H)
    ( reflects-div-mul-ℕ k d b H)
```
