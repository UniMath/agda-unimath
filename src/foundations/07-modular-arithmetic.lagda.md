---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.07-modular-arithmetic where

import foundations.06-universes
open foundations.06-universes public

--------------------------------------------------------------------------------

{- Section 7.1 The Curry-Howard interpretation -}

{- Definition 7.1.2 -}

-- We introduce the divisibility relation. --

div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → Id (mul-ℕ k m) n)

quotient-div-ℕ : (x y : ℕ) → div-ℕ x y → ℕ
quotient-div-ℕ x y H = pr1 H

eq-quotient-div-ℕ :
  (x y : ℕ) (H : div-ℕ x y) → Id (mul-ℕ (quotient-div-ℕ x y H) x) y
eq-quotient-div-ℕ x y H = pr2 H

eq-quotient-div-ℕ' :
  (x y : ℕ) (H : div-ℕ x y) → Id (mul-ℕ x (quotient-div-ℕ x y H)) y
eq-quotient-div-ℕ' x y H =
  commutative-mul-ℕ x (quotient-div-ℕ x y H) ∙ eq-quotient-div-ℕ x y H

concatenate-eq-div-ℕ :
  {x y z : ℕ} → Id x y → div-ℕ y z → div-ℕ x z
concatenate-eq-div-ℕ refl p = p

concatenate-div-eq-ℕ :
  {x y z : ℕ} → div-ℕ x y → Id y z → div-ℕ x z
concatenate-div-eq-ℕ p refl = p

concatenate-eq-div-eq-ℕ :
  {x y z w : ℕ} → Id x y → div-ℕ y z → Id z w → div-ℕ x w
concatenate-eq-div-eq-ℕ refl p refl = p

is-even-ℕ : ℕ → UU lzero
is-even-ℕ n = div-ℕ two-ℕ n

is-odd-ℕ : ℕ → UU lzero
is-odd-ℕ n = ¬ (is-even-ℕ n)

{- Example 7.1.4 -}

div-one-ℕ :
  (x : ℕ) → div-ℕ one-ℕ x
pr1 (div-one-ℕ x) = x
pr2 (div-one-ℕ x) = right-unit-law-mul-ℕ x

div-is-one-ℕ :
  (k x : ℕ) → is-one-ℕ k → div-ℕ k x
div-is-one-ℕ .one-ℕ x refl = div-one-ℕ x

div-zero-ℕ :
  (k : ℕ) → div-ℕ k zero-ℕ
pr1 (div-zero-ℕ k) = zero-ℕ
pr2 (div-zero-ℕ k) = left-zero-law-mul-ℕ k

div-is-zero-ℕ :
  (k x : ℕ) → is-zero-ℕ x → div-ℕ k x
div-is-zero-ℕ k .zero-ℕ refl = div-zero-ℕ k

{- Proposition 7.1.5 -}

{- In the following three constructions we show that if any two of the three
   numbers x, y, and x + y, is divisible by d, then so is the third. -}

div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (add-ℕ x y)
pr1 (div-add-ℕ d x y (pair n p) (pair m q)) = add-ℕ n m
pr2 (div-add-ℕ d x y (pair n p) (pair m q)) =
  ( right-distributive-mul-add-ℕ n m d) ∙
  ( ap-add-ℕ p q)

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (add-ℕ x y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) =
  pair zero-ℕ
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (add-ℕ x) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
pr1 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) = dist-ℕ m n
pr2 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) =
  is-injective-add-ℕ' (mul-ℕ m (succ-ℕ d))
    ( ( inv
        ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
          ( commutative-add-ℕ
            ( mul-ℕ m (succ-ℕ d))
            ( mul-ℕ (dist-ℕ m n) (succ-ℕ d))))) ∙ 
      ( ( ap
          ( mul-ℕ' (succ-ℕ d))
          ( is-additive-right-inverse-dist-ℕ m n
            ( leq-leq-mul-ℕ' m n d
              ( concatenate-eq-leq-eq-ℕ q
                ( leq-add-ℕ' y x)
                ( inv p))))) ∙
        ( p ∙ (ap (add-ℕ x) (inv q)))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (add-ℕ x y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (concatenate-div-eq-ℕ H2 (commutative-add-ℕ x y))

--------------------------------------------------------------------------------

{- Section 7.2 The congruence relations -}

{- Definition 7.2.1 -}

is-reflexive : {l1 l2 : Level} {A : UU l1} → (A → A → UU l2) → UU (l1 ⊔ l2)
is-reflexive {A = A} R = (x : A) → R x x

is-symmetric : {l1 l2 : Level} {A : UU l1} → (A → A → UU l2) → UU (l1 ⊔ l2)
is-symmetric {A = A} R = (x y : A) → R x y → R y x

is-transitive : {l1 l2 : Level} {A : UU l1} → (A → A → UU l2) → UU (l1 ⊔ l2)
is-transitive {A = A} R = (x y z : A) → R x y → R y z → R x z

{- Definition 7.2.2 -}

{- We define the congruence relation on ℕ and we do some bureaucracy that will
   help us in calculations involving the congruence relations. -}

cong-ℕ :
  ℕ → ℕ → ℕ → UU lzero
cong-ℕ k x y = div-ℕ k (dist-ℕ x y)

_≡_mod_ : ℕ → ℕ → ℕ → UU lzero
x ≡ y mod k = cong-ℕ k x y

concatenate-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 → cong-ℕ k x1 x4
concatenate-eq-cong-eq-ℕ k refl H refl = H

concatenate-eq-cong-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → cong-ℕ k x1 x3
concatenate-eq-cong-ℕ k refl H = H

concatenate-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  cong-ℕ k x1 x2 → Id x2 x3 → cong-ℕ k x1 x3
concatenate-cong-eq-ℕ k H refl = H

-- We show that cong-ℕ one-ℕ is the indiscrete equivalence relation --

is-indiscrete-cong-one-ℕ :
  (x y : ℕ) → cong-ℕ one-ℕ x y
is-indiscrete-cong-one-ℕ x y = div-one-ℕ (dist-ℕ x y)

-- We show that the congruence relation modulo 0 is discrete

is-discrete-cong-zero-ℕ :
  (x y : ℕ) → cong-ℕ zero-ℕ x y → Id x y
is-discrete-cong-zero-ℕ x y (pair k p) =
  eq-dist-ℕ x y ((inv p) ∙ (right-zero-law-mul-ℕ k))

{- Example 7.2.3 -}

cong-zero-ℕ :
  (k : ℕ) → cong-ℕ k k zero-ℕ
pr1 (cong-zero-ℕ k) = one-ℕ
pr2 (cong-zero-ℕ k) =
  (left-unit-law-mul-ℕ k) ∙ (inv (right-unit-law-dist-ℕ k))

{- Proposition 7.2.4 -}

-- We show that cong-ℕ is an equivalence relation.

refl-cong-ℕ :
  (k x : ℕ) → cong-ℕ k x x
pr1 (refl-cong-ℕ k x) = zero-ℕ
pr2 (refl-cong-ℕ k x) =
  (left-zero-law-mul-ℕ (succ-ℕ k)) ∙ (inv (dist-eq-ℕ x x refl))

cong-identification-ℕ :
  (k : ℕ) {x y : ℕ} → Id x y → cong-ℕ k x y
cong-identification-ℕ k {x} refl = refl-cong-ℕ k x

symm-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k y x
pr1 (symm-cong-ℕ k x y (pair d p)) = d
pr2 (symm-cong-ℕ k x y (pair d p)) = p ∙ (symmetric-dist-ℕ x y)

cong-zero-ℕ' :
  (k : ℕ) → cong-ℕ k zero-ℕ k
cong-zero-ℕ' k =
  symm-cong-ℕ k k zero-ℕ (cong-zero-ℕ k)

{- Before we show that cong-ℕ is transitive, we give some lemmas that will help 
   us showing that cong is an equivalence relation. They are basically 
   bureaucracy, manipulating already known facts. -}

-- Three elements can be ordered in 6 possible ways

cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ x y z =
  coprod
    ( coprod ((leq-ℕ x y) × (leq-ℕ y z)) ((leq-ℕ x z) × (leq-ℕ z y)))
    ( coprod
      ( coprod ((leq-ℕ y z) × (leq-ℕ z x)) ((leq-ℕ y x) × (leq-ℕ x z)))
      ( coprod ((leq-ℕ z x) × (leq-ℕ x y)) ((leq-ℕ z y) × (leq-ℕ y x))))

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ = inl (inr (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) =
  inl (map-coprod (pair star) (pair star) (decide-leq-ℕ y z))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ =
  inr (inl (inl (pair star star)))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) =
  inr (inl (map-coprod (pair star) (pair star) (decide-leq-ℕ z x)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ =
  inr (inr (map-coprod (pair star) (pair star) (decide-leq-ℕ x y)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  order-three-elements-ℕ x y z

{- We show that the distances of any three elements always add up, when they
   are added up in the right way :) -} 

cases-dist-ℕ :
  (x y z : ℕ) → UU lzero
cases-dist-ℕ x y z = 
  coprod
    ( Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z))
    ( coprod
      ( Id (add-ℕ (dist-ℕ y z) (dist-ℕ x z)) (dist-ℕ x y))
      ( Id (add-ℕ (dist-ℕ x z) (dist-ℕ x y)) (dist-ℕ y z)))

is-total-dist-ℕ :
  (x y z : ℕ) → cases-dist-ℕ x y z
is-total-dist-ℕ x y z with order-three-elements-ℕ x y z
is-total-dist-ℕ x y z | inl (inl (pair H1 H2)) =
  inl (triangle-equality-dist-ℕ x y z H1 H2)
is-total-dist-ℕ x y z | inl (inr (pair H1 H2)) = 
  inr
    ( inl
      ( ( commutative-add-ℕ (dist-ℕ y z) (dist-ℕ x z)) ∙
        ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ y z)) ∙
          ( triangle-equality-dist-ℕ x z y H1 H2))))
is-total-dist-ℕ x y z | inr (inl (inl (pair H1 H2))) =
  inr
    ( inl
      ( ( ap (add-ℕ (dist-ℕ y z)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ y z x H1 H2) ∙
          ( symmetric-dist-ℕ y x))))
is-total-dist-ℕ x y z | inr (inl (inr (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ x y)) ∙
        ( ( commutative-add-ℕ (dist-ℕ x z) (dist-ℕ y x)) ∙
          ( triangle-equality-dist-ℕ y x z H1 H2)))) 
is-total-dist-ℕ x y z | inr (inr (inl (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ' (dist-ℕ x y)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ z x y H1 H2) ∙
          ( symmetric-dist-ℕ z y))))
is-total-dist-ℕ x y z | inr (inr (inr (pair H1 H2))) =
  inl
    ( ( ap-add-ℕ (symmetric-dist-ℕ x y) (symmetric-dist-ℕ y z)) ∙
      ( ( commutative-add-ℕ (dist-ℕ y x) (dist-ℕ z y)) ∙
        ( ( triangle-equality-dist-ℕ z y x H1 H2) ∙
          ( symmetric-dist-ℕ z x))))

-- Finally, we show that cong-ℕ is transitive.

trans-cong-ℕ :
  (k x y z : ℕ) →
  cong-ℕ k x y → cong-ℕ k y z → cong-ℕ k x z
trans-cong-ℕ k x y z d e with is-total-dist-ℕ x y z
trans-cong-ℕ k x y z d e | inl α =
  concatenate-div-eq-ℕ (div-add-ℕ k (dist-ℕ x y) (dist-ℕ y z) d e) α
trans-cong-ℕ k x y z d e | inr (inl α) =
  div-right-summand-ℕ k (dist-ℕ y z) (dist-ℕ x z) e
    ( concatenate-div-eq-ℕ d (inv α))
trans-cong-ℕ k x y z d e | inr (inr α) =
  div-left-summand-ℕ k (dist-ℕ x z) (dist-ℕ x y) d
    ( concatenate-div-eq-ℕ e (inv α))

concatenate-cong-eq-cong-ℕ :
  {k x1 x2 x3 x4 : ℕ} →
  cong-ℕ k x1 x2 → Id x2 x3 → cong-ℕ k x3 x4 → cong-ℕ k x1 x4
concatenate-cong-eq-cong-ℕ {k} {x} {y} {.y} {z} H refl K =
  trans-cong-ℕ k x y z H K
  
concatenate-eq-cong-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 x5 x6 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 →
  cong-ℕ k x4 x5 → Id x5 x6 → cong-ℕ k x1 x6
concatenate-eq-cong-eq-cong-eq-ℕ k
  {x} {.x} {y} {.y} {z} {.z} refl H refl K refl =
  trans-cong-ℕ k x y z H K

--------------------------------------------------------------------------------

{- Section 7.3 The standard finite types -}

classical-Fin : ℕ → UU lzero
classical-Fin k = Σ ℕ (λ x → le-ℕ x k)

{- Definition 7.3.2 -}

-- We introduce the finite types as a family indexed by ℕ.

Fin : ℕ → UU lzero
Fin zero-ℕ = empty
Fin (succ-ℕ k) = coprod (Fin k) unit

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin k = inl

neg-one-Fin : {k : ℕ} → Fin (succ-ℕ k)
neg-one-Fin {k} = inr star

is-neg-one-Fin : {k : ℕ} → Fin k → UU lzero
is-neg-one-Fin {succ-ℕ k} x = Id x neg-one-Fin

{- Definition 7.3.4 -}

-- We define the inclusion of Fin k into ℕ.

nat-Fin : {k : ℕ} → Fin k → ℕ
nat-Fin {succ-ℕ k} (inl x) = nat-Fin x
nat-Fin {succ-ℕ k} (inr x) = k

{- Lemma 7.3.5 -}

-- We show that nat-Fin is bounded

strict-upper-bound-nat-Fin : {k : ℕ} (x : Fin k) → le-ℕ (nat-Fin x) k
strict-upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  transitive-le-ℕ
    ( nat-Fin x)
    ( k)
    ( succ-ℕ k)
    ( strict-upper-bound-nat-Fin x)
    ( succ-le-ℕ k)
strict-upper-bound-nat-Fin {succ-ℕ k} (inr star) =
  succ-le-ℕ k

-- We also give a non-strict upper bound for convenience

upper-bound-nat-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → leq-ℕ (nat-Fin x) k
upper-bound-nat-Fin {zero-ℕ} (inr star) = star
upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  preserves-leq-succ-ℕ (nat-Fin x) k (upper-bound-nat-Fin x)
upper-bound-nat-Fin {succ-ℕ k} (inr star) = refl-leq-ℕ (succ-ℕ k)

{- Proposition 7.3.6 -}

-- We show that nat-Fin is an injective function

neq-le-ℕ : {x y : ℕ} → le-ℕ x y → ¬ (Id x y)
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H = Peano-8 y ∘ inv
neq-le-ℕ {succ-ℕ x} {succ-ℕ y} H p = neq-le-ℕ H (is-injective-succ-ℕ p)

is-injective-nat-Fin : {k : ℕ} → is-injective (nat-Fin {k})
is-injective-nat-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-nat-Fin p)
is-injective-nat-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin x) p)
is-injective-nat-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin y) (inv p))
is-injective-nat-Fin {succ-ℕ k} {inr star} {inr star} p =
  refl

--------------------------------------------------------------------------------

{- Section 7.4 The natural numbers modulo k+1 -}

{- Definition 7.4.1 -}

is-split-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-split-surjective {A = A} {B} f = (b : B) → Σ A (λ a → Id (f a) b)

{- Definition 7.4.2 -}

-- We define the zero element of Fin k.

zero-Fin : {k : ℕ} → Fin (succ-ℕ k)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ k} = inl zero-Fin

is-zero-Fin : {k : ℕ} → Fin k → UU lzero
is-zero-Fin {succ-ℕ k} x = Id x zero-Fin

is-zero-Fin' : {k : ℕ} → Fin k → UU lzero
is-zero-Fin' {succ-ℕ k} x = Id zero-Fin x

is-nonzero-Fin : {k : ℕ} → Fin k → UU lzero
is-nonzero-Fin {succ-ℕ k} x = ¬ (is-zero-Fin x)

-- We define a function skip-zero-Fin in order to define succ-Fin.

skip-zero-Fin : {k : ℕ} → Fin k → Fin (succ-ℕ k)
skip-zero-Fin {succ-ℕ k} (inl x) = inl (skip-zero-Fin x)
skip-zero-Fin {succ-ℕ k} (inr star) = inr star

-- We define the successor function on Fin k.

succ-Fin : {k : ℕ} → Fin k → Fin k
succ-Fin {succ-ℕ k} (inl x) = skip-zero-Fin x
succ-Fin {succ-ℕ k} (inr star) = zero-Fin

{- Definition 7.4.3 -}

-- We define the modulo function

mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ k zero-ℕ = zero-Fin
mod-succ-ℕ k (succ-ℕ n) = succ-Fin (mod-succ-ℕ k n)

mod-two-ℕ : ℕ → Fin two-ℕ
mod-two-ℕ = mod-succ-ℕ one-ℕ

mod-three-ℕ : ℕ → Fin three-ℕ
mod-three-ℕ = mod-succ-ℕ two-ℕ

{- Lemma 7.4.4 -}

-- We prove three things to help calculating with nat-Fin.

is-zero-nat-zero-Fin : {k : ℕ} → is-zero-ℕ (nat-Fin (zero-Fin {k}))
is-zero-nat-zero-Fin {zero-ℕ} = refl 
is-zero-nat-zero-Fin {succ-ℕ k} = is-zero-nat-zero-Fin {k}

nat-skip-zero-Fin :
  {k : ℕ} (x : Fin k) → Id (nat-Fin (skip-zero-Fin x)) (succ-ℕ (nat-Fin x))
nat-skip-zero-Fin {succ-ℕ k} (inl x) = nat-skip-zero-Fin x
nat-skip-zero-Fin {succ-ℕ k} (inr star) = refl

nat-succ-Fin :
  {k : ℕ} (x : Fin k) → Id (nat-Fin (succ-Fin (inl x))) (succ-ℕ (nat-Fin x))
nat-succ-Fin {k} x = nat-skip-zero-Fin x

cong-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → cong-ℕ k (nat-Fin (succ-Fin x)) (succ-ℕ (nat-Fin x))
cong-nat-succ-Fin (succ-ℕ k) (inl x) =
  cong-identification-ℕ
    ( succ-ℕ k)
    { nat-Fin (succ-Fin (inl x))}
    { succ-ℕ (nat-Fin x)}
    ( nat-succ-Fin x)
cong-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-cong-ℕ
    ( succ-ℕ k)
    { nat-Fin {succ-ℕ k} zero-Fin}
    { zero-ℕ}
    { succ-ℕ k}
    ( is-zero-nat-zero-Fin {k})
    ( cong-zero-ℕ' (succ-ℕ k))

{- Proposition 7.4.5 -}

-- We show that (nat-Fin (mod-succ-ℕ n x)) is congruent to x modulo n+1. --

cong-nat-mod-succ-ℕ :
  (k x : ℕ) → cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
cong-nat-mod-succ-ℕ k zero-ℕ =
  cong-identification-ℕ (succ-ℕ k) (is-zero-nat-zero-Fin {k})
cong-nat-mod-succ-ℕ k (succ-ℕ x) =
  trans-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( cong-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x) )
    ( cong-nat-mod-succ-ℕ k x)

{- Proposition 7.4.6 -}

is-zero-div-ℕ :
  (d x : ℕ) → le-ℕ x d → div-ℕ d x → is-zero-ℕ x
is-zero-div-ℕ d zero-ℕ H D = refl
is-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) =
  ex-falso
    ( contradiction-le-ℕ
      ( succ-ℕ x) d H
      ( concatenate-leq-eq-ℕ d
        ( leq-add-ℕ' d (mul-ℕ k d)) p))

eq-cong-le-dist-ℕ :
  (k x y : ℕ) → le-ℕ (dist-ℕ x y) k → cong-ℕ k x y → Id x y
eq-cong-le-dist-ℕ k x y H K =
  eq-dist-ℕ x y (is-zero-div-ℕ k (dist-ℕ x y) H K)

strict-upper-bound-dist-ℕ :
  (b x y : ℕ) → le-ℕ x b → le-ℕ y b → le-ℕ (dist-ℕ x y) b
strict-upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ y H K = K
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) zero-ℕ H K = H
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) (succ-ℕ y) H K =
  preserves-le-succ-ℕ (dist-ℕ x y) b (strict-upper-bound-dist-ℕ b x y H K)

eq-cong-le-ℕ :
  (k x y : ℕ) → le-ℕ x k → le-ℕ y k → cong-ℕ k x y → Id x y
eq-cong-le-ℕ k x y H K =
  eq-cong-le-dist-ℕ k x y (strict-upper-bound-dist-ℕ k x y H K)

{- Theorem 7.4.7 -}

{- We show that if mod-succ-ℕ k x = mod-succ-ℕ k y, then x and y must be
   congruent modulo succ-ℕ n. This is the forward direction of the theorm. -}

cong-eq-mod-succ-ℕ :
  (k x y : ℕ) → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y) → cong-ℕ (succ-ℕ k) x y
cong-eq-mod-succ-ℕ k x y p =
  concatenate-cong-eq-cong-ℕ {succ-ℕ k} {x}
    ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
      ( cong-nat-mod-succ-ℕ k x))
    ( ap nat-Fin p)
    ( cong-nat-mod-succ-ℕ k y)

eq-cong-nat-Fin :
  (k : ℕ) (x y : Fin k) → cong-ℕ k (nat-Fin x) (nat-Fin y) → Id x y
eq-cong-nat-Fin (succ-ℕ k) x y H =
  is-injective-nat-Fin
    ( eq-cong-le-ℕ (succ-ℕ k) (nat-Fin x) (nat-Fin y)
      ( strict-upper-bound-nat-Fin x)
      ( strict-upper-bound-nat-Fin y)
      ( H))

eq-mod-succ-cong-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y)
eq-mod-succ-cong-ℕ k x y H =
  eq-cong-nat-Fin
    ( succ-ℕ k)
    ( mod-succ-ℕ k x)
    ( mod-succ-ℕ k y)
    ( trans-cong-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k x))
      ( x)
      ( nat-Fin (mod-succ-ℕ k y))
      ( cong-nat-mod-succ-ℕ k x)
      ( trans-cong-ℕ (succ-ℕ k) x y (nat-Fin (mod-succ-ℕ k y)) H
        ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k y)) y
          ( cong-nat-mod-succ-ℕ k y))))

-- We record some immediate corollaries

is-zero-Fin-div-ℕ :
  (k x : ℕ) → div-ℕ (succ-ℕ k) x → is-zero-Fin (mod-succ-ℕ k x)
is-zero-Fin-div-ℕ k x d =
  eq-mod-succ-cong-ℕ k x zero-ℕ
    ( concatenate-div-eq-ℕ d (inv (right-unit-law-dist-ℕ x)))

div-ℕ-is-zero-Fin :
  (k x : ℕ) → is-zero-Fin (mod-succ-ℕ k x) → div-ℕ (succ-ℕ k) x
div-ℕ-is-zero-Fin k x p =
  concatenate-div-eq-ℕ
    ( cong-eq-mod-succ-ℕ k x zero-ℕ p)
    ( right-unit-law-dist-ℕ x)

{- Theorem 7.4.8 -}

issec-nat-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mod-succ-ℕ k (nat-Fin x)) x
issec-nat-Fin {k} x =
  is-injective-nat-Fin
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k (nat-Fin x)))
      ( nat-Fin x)
      ( strict-upper-bound-nat-Fin (mod-succ-ℕ k (nat-Fin x)))
      ( strict-upper-bound-nat-Fin x)
      ( cong-nat-mod-succ-ℕ k (nat-Fin x)))

is-split-surjective-mod-succ-ℕ :
  {k : ℕ} → is-split-surjective (mod-succ-ℕ k)
pr1 (is-split-surjective-mod-succ-ℕ {k} x) = nat-Fin x
pr2 (is-split-surjective-mod-succ-ℕ {k} x) = issec-nat-Fin x

--------------------------------------------------------------------------------

{- Section 7.5 The cyclic group structure on the finite types -}

{- Definition 7.5.1 -}

-- Addition on finite sets --

add-Fin : {k : ℕ} → Fin k → Fin k → Fin k
add-Fin {succ-ℕ k} x y = mod-succ-ℕ k (add-ℕ (nat-Fin x) (nat-Fin y))

add-Fin' : {k : ℕ} → Fin k → Fin k → Fin k
add-Fin' x y = add-Fin y x

-- We define an action on paths of add-Fin on the two arguments at once.

ap-add-Fin :
  {k : ℕ} {x y x' y' : Fin k} →
  Id x x' → Id y y' → Id (add-Fin x y) (add-Fin x' y')
ap-add-Fin p q = ap-binary add-Fin p q

-- The negative of an element of Fin k --

neg-Fin :
  {k : ℕ} → Fin k → Fin k
neg-Fin {succ-ℕ k} x =
  mod-succ-ℕ k (dist-ℕ (nat-Fin x) (succ-ℕ k))

{- Remark 7.5.2 -}

cong-is-zero-nat-zero-Fin :
  {k : ℕ} → cong-ℕ (succ-ℕ k) (nat-Fin (zero-Fin {k})) zero-ℕ
cong-is-zero-nat-zero-Fin {k} = cong-nat-mod-succ-ℕ k zero-ℕ

cong-add-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (add-Fin x y)) (add-ℕ (nat-Fin x) (nat-Fin y))
cong-add-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (add-ℕ (nat-Fin x) (nat-Fin y))

cong-neg-Fin :
  {k : ℕ} (x : Fin k) →
  cong-ℕ k (nat-Fin (neg-Fin x)) (dist-ℕ (nat-Fin x) k)
cong-neg-Fin {succ-ℕ k} x = 
  cong-nat-mod-succ-ℕ k (dist-ℕ (nat-Fin x) (succ-ℕ k))

{- Proposition 7.5.3 -}

-- We show that congruence is translation invariant --

translation-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (add-ℕ z x) (add-ℕ z y)
pr1 (translation-invariant-cong-ℕ k x y z (pair d p)) = d
pr2 (translation-invariant-cong-ℕ k x y z (pair d p)) =
  p ∙ inv (translation-invariant-dist-ℕ z x y)

translation-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (add-ℕ x z) (add-ℕ y z)
translation-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-add-ℕ x z)
    ( translation-invariant-cong-ℕ k x y z H)
    ( commutative-add-ℕ z y)

step-invariant-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k (succ-ℕ x) (succ-ℕ y)
step-invariant-cong-ℕ k x y = translation-invariant-cong-ℕ' k x y one-ℕ

reflects-cong-add-ℕ :
  {k : ℕ} (x : ℕ) {y z : ℕ} → cong-ℕ k (add-ℕ x y) (add-ℕ x z) → cong-ℕ k y z
pr1 (reflects-cong-add-ℕ {k} x {y} {z} (pair d p)) = d
pr2 (reflects-cong-add-ℕ {k} x {y} {z} (pair d p)) =
  p ∙ translation-invariant-dist-ℕ x y z

reflects-cong-add-ℕ' :
  {k : ℕ} (x : ℕ) {y z : ℕ} → cong-ℕ k (add-ℕ' x y) (add-ℕ' x z) → cong-ℕ k y z
reflects-cong-add-ℕ' {k} x {y} {z} H =
  reflects-cong-add-ℕ x {y} {z}
    ( concatenate-eq-cong-eq-ℕ k
      ( commutative-add-ℕ x y)
      ( H)
      ( commutative-add-ℕ z x))

-- We show that addition respects the congruence relation --

congruence-add-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k y y' → cong-ℕ k (add-ℕ x y) (add-ℕ x' y')
congruence-add-ℕ k {x} {y} {x'} {y'} H K =
  trans-cong-ℕ k (add-ℕ x y) (add-ℕ x y') (add-ℕ x' y')
    ( translation-invariant-cong-ℕ k y y' x K)
    ( translation-invariant-cong-ℕ' k x x' y' H)

mod-succ-add-ℕ :
  (k x y : ℕ) →
  Id (mod-succ-ℕ k (add-ℕ x y)) (add-Fin (mod-succ-ℕ k x) (mod-succ-ℕ k y))
mod-succ-add-ℕ k x y =
  eq-mod-succ-cong-ℕ k
    ( add-ℕ x y)
    ( add-ℕ (nat-Fin (mod-succ-ℕ k x)) (nat-Fin (mod-succ-ℕ k y)))
    ( congruence-add-ℕ
      ( succ-ℕ k)
      { x}
      { y}
      { nat-Fin (mod-succ-ℕ k x)}
      { nat-Fin (mod-succ-ℕ k y)}
      ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
        ( cong-nat-mod-succ-ℕ k x))
      ( symm-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k y)) y
        ( cong-nat-mod-succ-ℕ k y)))

{- Theorem 7.5.4 -}

-- We show that addition is commutative --

commutative-add-Fin : {k : ℕ} (x y : Fin k) → Id (add-Fin x y) (add-Fin y x)
commutative-add-Fin {succ-ℕ k} x y =
  ap (mod-succ-ℕ k) (commutative-add-ℕ (nat-Fin x) (nat-Fin y))

-- We show that addition is associative --

associative-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (add-Fin (add-Fin x y) z) (add-Fin x (add-Fin y z))
associative-add-Fin {succ-ℕ k} x y z =
  eq-mod-succ-cong-ℕ k
    ( add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z))
    ( add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z)}
      { x2 = add-ℕ (add-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = add-ℕ (nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z))}
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (add-Fin x y)}
        { y = nat-Fin z}
        { x' = add-ℕ (nat-Fin x) (nat-Fin y)}
        { y' = nat-Fin z}
        ( cong-add-Fin x y)
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin x}
        { y = add-ℕ (nat-Fin y) (nat-Fin z)}
        { x' = nat-Fin x}
        { y' = nat-Fin (add-Fin y z)}
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin x))
        ( symm-cong-ℕ
          ( succ-ℕ k)
          ( nat-Fin (add-Fin y z))
          ( add-ℕ (nat-Fin y) (nat-Fin z))
          ( cong-add-Fin y z))))

-- We show that addition satisfies the right unit law --

right-unit-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin x zero-Fin) x
right-unit-law-add-Fin {k} x =
  ( eq-mod-succ-cong-ℕ k
    ( add-ℕ (nat-Fin x) (nat-Fin {succ-ℕ k} zero-Fin))
    ( add-ℕ (nat-Fin x) zero-ℕ)
    ( congruence-add-ℕ
      ( succ-ℕ k)
      { x = nat-Fin {succ-ℕ k} x}
      { y = nat-Fin {succ-ℕ k} zero-Fin}
      { x' = nat-Fin x}
      { y' = zero-ℕ}
      ( refl-cong-ℕ (succ-ℕ k) (nat-Fin {succ-ℕ k} x))
      ( cong-is-zero-nat-zero-Fin {k}))) ∙
  ( issec-nat-Fin x)

left-unit-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin zero-Fin x) x
left-unit-law-add-Fin {k} x =
  ( commutative-add-Fin zero-Fin x) ∙
  ( right-unit-law-add-Fin x)

-- We show that addition satisfies the left inverse law --

left-inverse-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-zero-Fin (add-Fin (neg-Fin x) x)
left-inverse-law-add-Fin {k} x =
  eq-mod-succ-cong-ℕ k
    ( add-ℕ (nat-Fin (neg-Fin x)) (nat-Fin x))
    ( zero-ℕ)
    ( concatenate-cong-eq-cong-ℕ
      { succ-ℕ k}
      { x1 = add-ℕ (nat-Fin (neg-Fin x)) (nat-Fin x)}
      { x2 = add-ℕ (dist-ℕ (nat-Fin x) (succ-ℕ k)) (nat-Fin x)}
      { x3 = succ-ℕ k}
      { x4 = zero-ℕ}
      ( translation-invariant-cong-ℕ' (succ-ℕ k)
        ( nat-Fin (neg-Fin x))
        ( dist-ℕ (nat-Fin x) (succ-ℕ k))
        ( nat-Fin x)
        ( cong-neg-Fin x))
      ( is-difference-dist-ℕ' (nat-Fin x) (succ-ℕ k)
        ( upper-bound-nat-Fin (inl x)))
      ( cong-zero-ℕ' (succ-ℕ k)))

right-inverse-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-zero-Fin (add-Fin x (neg-Fin x))
right-inverse-law-add-Fin x =
  ( commutative-add-Fin x (neg-Fin x)) ∙ (left-inverse-law-add-Fin x)

--------------------------------------------------------------------------------

{- Exercises -}

{- Exercise 7.1 -}

-- See Proposition 7.1.5

{- Exercise 7.2 -}

-- We show that the divisibility relation is a poset

refl-div-ℕ : (x : ℕ) → div-ℕ x x
pr1 (refl-div-ℕ x) = one-ℕ
pr2 (refl-div-ℕ x) = left-unit-law-mul-ℕ x

antisymmetric-div-ℕ :
  (x y : ℕ) → div-ℕ x y → div-ℕ y x → Id x y
antisymmetric-div-ℕ zero-ℕ zero-ℕ H K = refl
antisymmetric-div-ℕ zero-ℕ (succ-ℕ y) (pair k p) K =
  inv (right-zero-law-mul-ℕ k) ∙ p
antisymmetric-div-ℕ (succ-ℕ x) zero-ℕ H (pair l q) =
  inv q ∙ right-zero-law-mul-ℕ l
antisymmetric-div-ℕ (succ-ℕ x) (succ-ℕ y) (pair k p) (pair l q) =
  ( inv (left-unit-law-mul-ℕ (succ-ℕ x))) ∙
  ( ( ap ( mul-ℕ' (succ-ℕ x))
         ( inv
           ( is-one-right-is-one-mul-ℕ l k
             ( is-one-is-left-unit-mul-ℕ (mul-ℕ l k) x
               ( ( associative-mul-ℕ l k (succ-ℕ x)) ∙
                 ( ap (mul-ℕ l) p ∙ q)))))) ∙
    ( p))

transitive-div-ℕ :
  (x y z : ℕ) → div-ℕ x y → div-ℕ y z → div-ℕ x z
pr1 (transitive-div-ℕ x y z (pair k p) (pair l q)) = mul-ℕ l k
pr2 (transitive-div-ℕ x y z (pair k p) (pair l q)) =
  associative-mul-ℕ l k x ∙ (ap (mul-ℕ l) p ∙ q)

div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (mul-ℕ k y)
div-mul-ℕ k x y H =
  transitive-div-ℕ x y (mul-ℕ k y) H (pair k refl)

preserves-div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ (mul-ℕ k x) (mul-ℕ k y)
pr1 (preserves-div-mul-ℕ k x y (pair q p)) = q
pr2 (preserves-div-mul-ℕ k x y (pair q p)) =
  ( inv (associative-mul-ℕ q k x)) ∙
    ( ( ap (mul-ℕ' x) (commutative-mul-ℕ q k)) ∙
      ( ( associative-mul-ℕ k q x) ∙
        ( ap (mul-ℕ k) p)))

reflects-div-mul-ℕ :
  (k x y : ℕ) → is-nonzero-ℕ k → div-ℕ (mul-ℕ k x) (mul-ℕ k y) → div-ℕ x y
pr1 (reflects-div-mul-ℕ k x y H (pair q p)) = q
pr2 (reflects-div-mul-ℕ k x y H (pair q p)) =
  is-injective-mul-ℕ k H
    ( ( inv (associative-mul-ℕ k q x)) ∙
      ( ( ap (mul-ℕ' x) (commutative-mul-ℕ k q)) ∙
        ( ( associative-mul-ℕ q k x) ∙
          ( p))))

div-quotient-div-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) → is-nonzero-ℕ d →
  div-ℕ (mul-ℕ d x) y → div-ℕ x (quotient-div-ℕ d y H)
div-quotient-div-div-ℕ x y d H f K =
  reflects-div-mul-ℕ d x
    ( quotient-div-ℕ d y H)
    ( f)
    ( tr (div-ℕ (mul-ℕ d x)) (inv (eq-quotient-div-ℕ' d y H)) K)

div-div-quotient-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) →
  div-ℕ x (quotient-div-ℕ d y H) → div-ℕ (mul-ℕ d x) y
div-div-quotient-div-ℕ x y d H K =
  tr ( div-ℕ (mul-ℕ d x))
     ( eq-quotient-div-ℕ' d y H)
     ( preserves-div-mul-ℕ d x (quotient-div-ℕ d y H) K)

-- We conclude that 0 | x implies x = 0 and x | 1 implies x = 1.

is-zero-div-zero-ℕ : (x : ℕ) → div-ℕ zero-ℕ x → is-zero-ℕ x
is-zero-div-zero-ℕ x H = antisymmetric-div-ℕ x zero-ℕ (div-zero-ℕ x) H

is-zero-is-zero-div-ℕ : (x y : ℕ) → div-ℕ x y → is-zero-ℕ x → is-zero-ℕ y
is-zero-is-zero-div-ℕ .zero-ℕ y d refl = is-zero-div-zero-ℕ y d

is-one-div-one-ℕ : (x : ℕ) → div-ℕ x one-ℕ → is-one-ℕ x
is-one-div-one-ℕ x H = antisymmetric-div-ℕ x one-ℕ H (div-one-ℕ x)

is-one-div-ℕ : (x y : ℕ) → div-ℕ x y → div-ℕ x (succ-ℕ y) → is-one-ℕ x
is-one-div-ℕ x y H K = is-one-div-one-ℕ x (div-right-summand-ℕ x y one-ℕ H K)

div-eq-ℕ : (x y : ℕ) → Id x y → div-ℕ x y
div-eq-ℕ x .x refl = refl-div-ℕ x

-- Bureaucracy

eq-cong-zero-ℕ : (x y : ℕ) → cong-ℕ zero-ℕ x y → Id x y
eq-cong-zero-ℕ x y H =
  eq-dist-ℕ x y (is-zero-div-zero-ℕ (dist-ℕ x y) H)

{- Exercise 7.3 -}

div-factorial-is-nonzero-ℕ :
  (n x : ℕ) → leq-ℕ x n → is-nonzero-ℕ x → div-ℕ x (factorial-ℕ n)
div-factorial-is-nonzero-ℕ zero-ℕ zero-ℕ l H = ex-falso (H refl)
div-factorial-is-nonzero-ℕ (succ-ℕ n) x l H with
  decide-leq-succ-ℕ x n l
... | inl l' =
  transitive-div-ℕ x
    ( factorial-ℕ n)
    ( factorial-ℕ (succ-ℕ n))
    ( div-factorial-is-nonzero-ℕ n x l' H)
    ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (factorial-ℕ n)))
... | inr refl = pair (factorial-ℕ n) refl

{- Exercise 7.4 -}

one-Fin : {k : ℕ} → Fin (succ-ℕ k)
one-Fin {k} = mod-succ-ℕ k one-ℕ

is-one-Fin : {k : ℕ} → Fin k → UU lzero
is-one-Fin {succ-ℕ k} x = Id x one-Fin

is-zero-or-one-Fin-two-ℕ :
  (x : Fin two-ℕ) → coprod (is-zero-Fin x) (is-one-Fin x)
is-zero-or-one-Fin-two-ℕ (inl (inr star)) = inl refl
is-zero-or-one-Fin-two-ℕ (inr star) = inr refl

is-one-nat-one-Fin :
  (k : ℕ) → is-one-ℕ (nat-Fin (one-Fin {succ-ℕ k}))
is-one-nat-one-Fin zero-ℕ = refl
is-one-nat-one-Fin (succ-ℕ k) = is-one-nat-one-Fin k

is-add-one-succ-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (succ-Fin x) (add-Fin x one-Fin)
is-add-one-succ-Fin {zero-ℕ} (inr star) = refl
is-add-one-succ-Fin {succ-ℕ k} x =
  ( ap succ-Fin (inv (issec-nat-Fin x))) ∙
  ( ap ( mod-succ-ℕ  (succ-ℕ k))
       ( ap (add-ℕ (nat-Fin x)) (inv (is-one-nat-one-Fin (succ-ℕ k)))))

-- We conclude the successor laws for addition on Fin k

right-successor-law-add-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin x (succ-Fin y)) (succ-Fin (add-Fin x y))
right-successor-law-add-Fin {succ-ℕ k} x y =
  ( ap (add-Fin x) (is-add-one-succ-Fin y)) ∙
  ( ( inv (associative-add-Fin x y one-Fin)) ∙
    ( inv (is-add-one-succ-Fin (add-Fin x y))))

left-successor-law-add-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin (succ-Fin x) y) (succ-Fin (add-Fin x y))
left-successor-law-add-Fin x y =
  commutative-add-Fin (succ-Fin x) y ∙
  ( ( right-successor-law-add-Fin y x) ∙
    ( ap succ-Fin (commutative-add-Fin y x)))

{- Exercise 7.5 -}

-- We introduce the observational equality on finite sets.

Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

-- Exercise 7.5 (a)

refl-Eq-Fin : {k : ℕ} (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin {succ-ℕ k} (inl x) = refl-Eq-Fin x
refl-Eq-Fin {succ-ℕ k} (inr x) = star

Eq-Fin-eq : {k : ℕ} {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq {k} refl = refl-Eq-Fin {k} _

eq-Eq-Fin :
  {k : ℕ} {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin {succ-ℕ k} {inl x} {inl y} e = ap inl (eq-Eq-Fin e)
eq-Eq-Fin {succ-ℕ k} {inr star} {inr star} star = refl

-- Exercise 7.5 (b)

is-injective-inl-Fin : {k : ℕ} → is-injective (inl-Fin k)
is-injective-inl-Fin p = eq-Eq-Fin (Eq-Fin-eq p)

-- Exercise 7.5 (c)

neq-zero-succ-Fin :
  {k : ℕ} {x : Fin k} → is-nonzero-Fin (succ-Fin (inl-Fin k x))
neq-zero-succ-Fin {succ-ℕ k} {inl x} p =
  neq-zero-succ-Fin (is-injective-inl-Fin p)
neq-zero-succ-Fin {succ-ℕ k} {inr star} p =
  Eq-Fin-eq {succ-ℕ (succ-ℕ k)} {inr star} {zero-Fin} p

-- Exercise 7.5 (d)

is-injective-skip-zero-Fin : {k : ℕ} → is-injective (skip-zero-Fin {k})
is-injective-skip-zero-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin (is-injective-inl-Fin p))
is-injective-skip-zero-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (Eq-Fin-eq p)
is-injective-skip-zero-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (Eq-Fin-eq p)
is-injective-skip-zero-Fin {succ-ℕ k} {inr star} {inr star} p = refl

is-injective-succ-Fin : {k : ℕ} → is-injective (succ-Fin {k})
is-injective-succ-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin {k} {x} {y} p)
is-injective-succ-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl x} (ap inl p))
is-injective-succ-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl y} (ap inl (inv p)))
is-injective-succ-Fin {succ-ℕ k} {inr star} {inr star} p = refl

{- Exercise 7.6 -}

-- We define the negative two element of Fin k.

neg-two-Fin :
  {k : ℕ} → Fin (succ-ℕ k)
neg-two-Fin {zero-ℕ} = inr star
neg-two-Fin {succ-ℕ k} = inl (inr star)

-- We define a function skip-neg-two-Fin in order to define pred-Fin.

skip-neg-two-Fin :
  {k : ℕ} → Fin k → Fin (succ-ℕ k)
skip-neg-two-Fin {succ-ℕ k} (inl x) = inl (inl x)
skip-neg-two-Fin {succ-ℕ k} (inr x) = neg-one-Fin {succ-ℕ k}

-- We define the predecessor function on Fin k.

pred-Fin : {k : ℕ} → Fin k → Fin k
pred-Fin {succ-ℕ k} (inl x) = skip-neg-two-Fin (pred-Fin x)
pred-Fin {succ-ℕ k} (inr x) = neg-two-Fin

-- We now turn to the exercise.

pred-zero-Fin :
  {k : ℕ} → is-neg-one-Fin (pred-Fin {succ-ℕ k} zero-Fin)
pred-zero-Fin {zero-ℕ} = refl
pred-zero-Fin {succ-ℕ k} = ap skip-neg-two-Fin (pred-zero-Fin {k})

succ-skip-neg-two-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) →
  Id (succ-Fin (skip-neg-two-Fin x)) (inl (succ-Fin x))
succ-skip-neg-two-Fin {zero-ℕ} (inr star) = refl
succ-skip-neg-two-Fin {succ-ℕ k} (inl x) = refl
succ-skip-neg-two-Fin {succ-ℕ k} (inr star) = refl

issec-pred-Fin :
  {k : ℕ} (x : Fin k) → Id (succ-Fin (pred-Fin x)) x
issec-pred-Fin {succ-ℕ zero-ℕ} (inr star) = refl
issec-pred-Fin {succ-ℕ (succ-ℕ k)} (inl x) =
  succ-skip-neg-two-Fin (pred-Fin x) ∙ ap inl (issec-pred-Fin x)
issec-pred-Fin {succ-ℕ (succ-ℕ k)} (inr star) = refl

isretr-pred-Fin :
  {k : ℕ} (x : Fin k) → Id (pred-Fin (succ-Fin x)) x
isretr-pred-Fin {succ-ℕ zero-ℕ} (inr star) = refl
isretr-pred-Fin {succ-ℕ (succ-ℕ k)} (inl (inl x)) =
  ap skip-neg-two-Fin (isretr-pred-Fin (inl x))
isretr-pred-Fin {succ-ℕ (succ-ℕ k)} (inl (inr star)) = refl
isretr-pred-Fin {succ-ℕ (succ-ℕ k)} (inr star) = pred-zero-Fin

{- Exercise 7.7 -}

-- We introduce the type of bounded natural numbers

nat-classical-Fin : (k : ℕ) → classical-Fin k → ℕ
nat-classical-Fin k = pr1

-- We introduce an observational equality relation on the bounded naturals

Eq-classical-Fin : (k : ℕ) (x y : classical-Fin k) → UU lzero
Eq-classical-Fin k x y = Id (nat-classical-Fin k x) (nat-classical-Fin k y)

eq-succ-classical-Fin :
  (k : ℕ) (x y : classical-Fin k) → Id {A = classical-Fin k} x y →
  Id {A = classical-Fin (succ-ℕ k)}
     ( pair (succ-ℕ (pr1 x)) (pr2 x))
     ( pair (succ-ℕ (pr1 y)) (pr2 y))
eq-succ-classical-Fin k x .x refl = refl

eq-Eq-classical-Fin :
  (k : ℕ) (x y : classical-Fin k) → Eq-classical-Fin k x y → Id x y
eq-Eq-classical-Fin (succ-ℕ k) (pair zero-ℕ star) (pair zero-ℕ star) e = refl
eq-Eq-classical-Fin (succ-ℕ k) (pair (succ-ℕ x) p) (pair (succ-ℕ y) q) e =
  eq-succ-classical-Fin k
    ( pair x p)
    ( pair y q)
    ( eq-Eq-classical-Fin k (pair x p) (pair y q) (is-injective-succ-ℕ e))

{- We define maps back and forth between the standard finite sets and the
   bounded natural numbers -}

standard-classical-Fin : {k : ℕ} → classical-Fin k → Fin k
standard-classical-Fin {succ-ℕ k} (pair x H) = mod-succ-ℕ k x

classical-standard-Fin :
  (k : ℕ) → Fin k → classical-Fin k
pr1 (classical-standard-Fin k x) = nat-Fin x
pr2 (classical-standard-Fin k x) = strict-upper-bound-nat-Fin x

{- We show that these maps are mutual inverses -}

issec-classical-standard-Fin :
  {k : ℕ} (x : Fin k) →
  Id (standard-classical-Fin (classical-standard-Fin k x)) x
issec-classical-standard-Fin {succ-ℕ k} x = issec-nat-Fin x

isretr-classical-standard-Fin :
  {k : ℕ} (x : classical-Fin k) →
  Id (classical-standard-Fin k (standard-classical-Fin x)) x
isretr-classical-standard-Fin {succ-ℕ k} (pair x p) =
  eq-Eq-classical-Fin (succ-ℕ k)
    ( classical-standard-Fin (succ-ℕ k) (standard-classical-Fin (pair x p)))
    ( pair x p)
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k x))
      ( x)
      ( strict-upper-bound-nat-Fin (mod-succ-ℕ k x))
      ( p)
      ( cong-nat-mod-succ-ℕ k x))

{- Exercise 7.8 -}

{- We define the multiplication on the types Fin k. -}

mul-Fin :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin {succ-ℕ k} x y = mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

mul-Fin' :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin' {k} x y = mul-Fin y x

ap-mul-Fin :
  {k : ℕ} {x y x' y' : Fin k} →
  Id x x' → Id y y' → Id (mul-Fin x y) (mul-Fin x' y')
ap-mul-Fin p q = ap-binary mul-Fin p q

-- Exercise 7.8 (a)

cong-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (mul-Fin x y)) (mul-ℕ (nat-Fin x) (nat-Fin y))
cong-mul-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

-- Exercise 7.8 (b)

-- We show that congruence is invariant under scalar multiplication --

scalar-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y →  cong-ℕ k (mul-ℕ z x) (mul-ℕ z y)
pr1 (scalar-invariant-cong-ℕ k x y z (pair d p)) = mul-ℕ z d
pr2 (scalar-invariant-cong-ℕ k x y z (pair d p)) =
  ( associative-mul-ℕ z d k) ∙
    ( ( ap (mul-ℕ z) p) ∙
      ( left-distributive-mul-dist-ℕ x y z))

scalar-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (mul-ℕ x z) (mul-ℕ y z)
scalar-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-mul-ℕ x z)
    ( scalar-invariant-cong-ℕ k x y z H)
    ( commutative-mul-ℕ z y)

-- We show that multiplication respects the congruence relation --

congruence-mul-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ  k x x' → cong-ℕ k y y' → cong-ℕ k (mul-ℕ x y) (mul-ℕ x' y')
congruence-mul-ℕ k {x} {y} {x'} {y'} H K =
  trans-cong-ℕ k (mul-ℕ x y) (mul-ℕ x y') (mul-ℕ x' y')
    ( scalar-invariant-cong-ℕ k y y' x K)
    ( scalar-invariant-cong-ℕ' k x x' y' H)

-- Exercise 7.8 (c)

associative-mul-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (mul-Fin x y) z) (mul-Fin x (mul-Fin y z))
associative-mul-Fin {succ-ℕ k} x y z =
  eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z))
    ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z)}
      { x2 = mul-ℕ (mul-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (mul-Fin x y)}
        { y = nat-Fin z}
        ( cong-mul-Fin x y)
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-mul-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symm-cong-ℕ
        ( succ-ℕ k)
        ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
        ( mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z)))
        ( congruence-mul-ℕ
          ( succ-ℕ k)
          { x = nat-Fin x}
          { y = nat-Fin (mul-Fin y z)}
          ( refl-cong-ℕ (succ-ℕ k) (nat-Fin x))
          ( cong-mul-Fin y z))))

commutative-mul-Fin :
  {k : ℕ} (x y : Fin k) → Id (mul-Fin x y) (mul-Fin y x)
commutative-mul-Fin {succ-ℕ k} x y =
  eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin y))
    ( mul-ℕ (nat-Fin y) (nat-Fin x))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( commutative-mul-ℕ (nat-Fin x) (nat-Fin y)))

left-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin one-Fin x) x
left-unit-law-mul-Fin {zero-ℕ} (inr star) = refl
left-unit-law-mul-Fin {succ-ℕ k} x =
  ( eq-mod-succ-cong-ℕ (succ-ℕ k)
    ( mul-ℕ (nat-Fin (one-Fin {succ-ℕ k})) (nat-Fin x))
    ( nat-Fin x)
    ( cong-identification-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( ( ap ( mul-ℕ' (nat-Fin x))
             ( is-one-nat-one-Fin k)) ∙
        ( left-unit-law-mul-ℕ (nat-Fin x))))) ∙
  ( issec-nat-Fin x)

right-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x one-Fin) x
right-unit-law-mul-Fin x =
  ( commutative-mul-Fin x one-Fin) ∙
  ( left-unit-law-mul-Fin x)

left-zero-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin zero-Fin x) zero-Fin
left-zero-law-mul-Fin {k} x =
  ( eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin (zero-Fin {k})) (nat-Fin x))
    ( nat-Fin (zero-Fin {k}))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      { mul-ℕ (nat-Fin (zero-Fin {k})) (nat-Fin x)}
      { nat-Fin (zero-Fin {k})}
      ( ( ap (mul-ℕ' (nat-Fin x)) (is-zero-nat-zero-Fin {k})) ∙
        ( inv (is-zero-nat-zero-Fin {k}))))) ∙
  ( issec-nat-Fin (zero-Fin {k}))

right-zero-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x zero-Fin) zero-Fin
right-zero-law-mul-Fin x =
  ( commutative-mul-Fin x zero-Fin) ∙
  ( left-zero-law-mul-Fin x)

left-distributive-mul-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin x (add-Fin y z)) (add-Fin (mul-Fin x y) (mul-Fin x z))
left-distributive-mul-add-Fin {succ-ℕ k} x y z =
  eq-mod-succ-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( add-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin (mul-Fin x z)))
    ( concatenate-cong-eq-cong-ℕ
      { k = succ-ℕ k}
      { x1 = mul-ℕ ( nat-Fin x) (nat-Fin (add-Fin y z))}
      { x2 = mul-ℕ ( nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x3 = add-ℕ ( mul-ℕ (nat-Fin x) (nat-Fin y))
                   ( mul-ℕ (nat-Fin x) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin (mul-Fin x z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin x}
        { y = nat-Fin (add-Fin y z)}
        { x' = nat-Fin x}
        { y' = add-ℕ (nat-Fin y) (nat-Fin z)}
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin x))
        ( cong-add-Fin y z))
      ( left-distributive-mul-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symm-cong-ℕ (succ-ℕ k)
        ( add-ℕ ( nat-Fin (mul-Fin x y))
                ( nat-Fin (mul-Fin x z)))
        ( add-ℕ ( mul-ℕ (nat-Fin x) (nat-Fin y))
                ( mul-ℕ (nat-Fin x) (nat-Fin z)))
        ( congruence-add-ℕ
          ( succ-ℕ k)
          { x = nat-Fin (mul-Fin x y)}
          { y = nat-Fin (mul-Fin x z)}
          { x' = mul-ℕ (nat-Fin x) (nat-Fin y)}
          { y' = mul-ℕ (nat-Fin x) (nat-Fin z)}
          ( cong-mul-Fin x y)
          ( cong-mul-Fin x z))))

right-distributive-mul-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (add-Fin x y) z) (add-Fin (mul-Fin x z) (mul-Fin y z))
right-distributive-mul-add-Fin {k} x y z =
  ( commutative-mul-Fin (add-Fin x y) z) ∙
  ( ( left-distributive-mul-add-Fin z x y) ∙
    ( ap-add-Fin (commutative-mul-Fin z x) (commutative-mul-Fin z y)))

add-add-neg-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin x (add-Fin (neg-Fin x) y)) y
add-add-neg-Fin {succ-ℕ k} x y =
  ( inv (associative-add-Fin x (neg-Fin x) y)) ∙
  ( ( ap (add-Fin' y) (right-inverse-law-add-Fin x)) ∙
    ( left-unit-law-add-Fin y))

add-neg-add-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin (neg-Fin x) (add-Fin x y)) y
add-neg-add-Fin {succ-ℕ k} x y =
  ( inv (associative-add-Fin (neg-Fin x) x y)) ∙
  ( ( ap (add-Fin' y) (left-inverse-law-add-Fin x)) ∙
    ( left-unit-law-add-Fin y))

is-injective-add-Fin :
  {k : ℕ} (x : Fin k) → is-injective (add-Fin x)
is-injective-add-Fin {k} x {y} {z} p =
  ( inv (add-neg-add-Fin x y)) ∙
  ( ( ap (add-Fin (neg-Fin x)) p) ∙
    ( add-neg-add-Fin x z))

mul-neg-one-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin neg-one-Fin x) (neg-Fin x)
mul-neg-one-Fin {k} x =
  is-injective-add-Fin x
    ( ( ( ap
          ( add-Fin' (mul-Fin neg-one-Fin x))
          ( inv (left-unit-law-mul-Fin x))) ∙
        ( ( inv (right-distributive-mul-add-Fin one-Fin neg-one-Fin x)) ∙
          ( ( ap
              ( mul-Fin' x)
              ( ( commutative-add-Fin one-Fin neg-one-Fin) ∙
                ( inv (is-add-one-succ-Fin neg-one-Fin)))) ∙
            ( left-zero-law-mul-Fin x)))) ∙
      ( inv (right-inverse-law-add-Fin x)))

-- We prove some further laws for the operations on Fin

is-one-neg-neg-one-Fin :
  {k : ℕ} → is-one-Fin {succ-ℕ k} (neg-Fin neg-one-Fin)
is-one-neg-neg-one-Fin {k} =
  eq-mod-succ-cong-ℕ k
    ( dist-ℕ k (succ-ℕ k))
    ( one-ℕ)
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( is-one-dist-succ-ℕ k))

is-neg-one-neg-one-Fin :
  {k : ℕ} → Id (neg-Fin {succ-ℕ k} one-Fin) neg-one-Fin
is-neg-one-neg-one-Fin {k} =
  is-injective-add-Fin one-Fin
    ( ( right-inverse-law-add-Fin one-Fin) ∙
      ( ( inv (left-inverse-law-add-Fin neg-one-Fin)) ∙
        ( ap (add-Fin' neg-one-Fin) is-one-neg-neg-one-Fin)))

is-add-neg-one-pred-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (pred-Fin x) (add-Fin x neg-one-Fin)
is-add-neg-one-pred-Fin {k} x =
  is-injective-succ-Fin
    ( ( issec-pred-Fin x) ∙
      ( ( ( ( inv (right-unit-law-add-Fin x)) ∙
            ( ap
              ( add-Fin x)
              ( inv
                ( ( ap (add-Fin' one-Fin) (inv is-neg-one-neg-one-Fin)) ∙
                  ( left-inverse-law-add-Fin one-Fin))))) ∙
          ( inv (associative-add-Fin x neg-one-Fin one-Fin))) ∙
        ( inv (is-add-one-succ-Fin (add-Fin x neg-one-Fin)))))

is-mul-neg-one-neg-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (neg-Fin x) (mul-Fin neg-one-Fin x)
is-mul-neg-one-neg-Fin x =
  is-injective-add-Fin x
    ( ( right-inverse-law-add-Fin x) ∙
      ( ( ( ( inv (left-zero-law-mul-Fin x)) ∙
            ( ap
              ( mul-Fin' x)
              ( inv
                ( ( ap (add-Fin one-Fin) (inv is-neg-one-neg-one-Fin)) ∙
                  ( right-inverse-law-add-Fin one-Fin))))) ∙
          ( right-distributive-mul-add-Fin one-Fin neg-one-Fin x)) ∙
        ( ap (add-Fin' (mul-Fin neg-one-Fin x)) (left-unit-law-mul-Fin x))))

neg-zero-Fin : {k : ℕ} → Id (neg-Fin (zero-Fin {k})) zero-Fin
neg-zero-Fin {k} =
  ( inv (left-unit-law-add-Fin (neg-Fin zero-Fin))) ∙
  ( right-inverse-law-add-Fin zero-Fin)

neg-succ-Fin :
  {k : ℕ} (x : Fin k) → Id (neg-Fin (succ-Fin x)) (pred-Fin (neg-Fin x))
neg-succ-Fin {succ-ℕ k} x =
  ( ap neg-Fin (is-add-one-succ-Fin x)) ∙
  ( ( is-mul-neg-one-neg-Fin (add-Fin x one-Fin)) ∙
    ( ( left-distributive-mul-add-Fin neg-one-Fin x one-Fin) ∙
      ( ( ap-add-Fin
          ( inv (is-mul-neg-one-neg-Fin x))
          ( inv (is-mul-neg-one-neg-Fin one-Fin) ∙ is-neg-one-neg-one-Fin)) ∙
        ( inv (is-add-neg-one-pred-Fin (neg-Fin x))))))

neg-pred-Fin :
  {k : ℕ} (x : Fin k) → Id (neg-Fin (pred-Fin x)) (succ-Fin (neg-Fin x))
neg-pred-Fin {succ-ℕ k} x =
  ( ap neg-Fin (is-add-neg-one-pred-Fin x)) ∙
  ( ( is-mul-neg-one-neg-Fin (add-Fin x neg-one-Fin)) ∙
    ( ( left-distributive-mul-add-Fin neg-one-Fin x neg-one-Fin) ∙
      ( ( ap-add-Fin
          ( inv (is-mul-neg-one-neg-Fin x))
          ( ( inv (is-mul-neg-one-neg-Fin neg-one-Fin)) ∙
            ( is-one-neg-neg-one-Fin))) ∙
        ( inv (is-add-one-succ-Fin (neg-Fin x))))))

distributive-neg-add-Fin :
  {k : ℕ} (x y : Fin k) →
  Id (neg-Fin (add-Fin x y)) (add-Fin (neg-Fin x) (neg-Fin y))
distributive-neg-add-Fin {succ-ℕ k} x y =
  ( is-mul-neg-one-neg-Fin (add-Fin x y)) ∙
  ( ( left-distributive-mul-add-Fin neg-one-Fin x y) ∙
    ( inv (ap-add-Fin (is-mul-neg-one-neg-Fin x) (is-mul-neg-one-neg-Fin y))))

left-predecessor-law-add-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin (pred-Fin x) y) (pred-Fin (add-Fin x y))
left-predecessor-law-add-Fin {succ-ℕ k} x y =
  ( ap
    ( add-Fin' y)
    ( is-add-neg-one-pred-Fin x ∙ commutative-add-Fin x neg-one-Fin)) ∙
  ( ( associative-add-Fin neg-one-Fin x y) ∙
    ( ( commutative-add-Fin neg-one-Fin (add-Fin x y)) ∙
      ( inv (is-add-neg-one-pred-Fin (add-Fin x y)))))

right-predecessor-law-add-Fin :
  {k : ℕ} (x y : Fin k) → Id (add-Fin x (pred-Fin y)) (pred-Fin (add-Fin x y))
right-predecessor-law-add-Fin {succ-ℕ k} x y =
  ( ap (add-Fin x) (is-add-neg-one-pred-Fin y)) ∙
  ( ( inv (associative-add-Fin x y neg-one-Fin)) ∙
    ( inv (is-add-neg-one-pred-Fin (add-Fin x y))))

left-negative-law-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  Id (mul-Fin (neg-Fin x) y) (neg-Fin (mul-Fin x y))
left-negative-law-mul-Fin {succ-ℕ k} x y =
  ( ap (mul-Fin' y) (is-mul-neg-one-neg-Fin x)) ∙
  ( ( associative-mul-Fin neg-one-Fin x y) ∙
    ( inv (is-mul-neg-one-neg-Fin (mul-Fin x y))))

right-negative-law-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  Id (mul-Fin x (neg-Fin y)) (neg-Fin (mul-Fin x y))
right-negative-law-mul-Fin {succ-ℕ k} x y =
  ( commutative-mul-Fin x (neg-Fin y)) ∙
  ( ( left-negative-law-mul-Fin y x) ∙
    ( ap neg-Fin (commutative-mul-Fin y x)))

{- Exercise 7.9 -}

-- We first prove two lemmas

leq-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → leq-ℕ (nat-Fin (succ-Fin x)) (succ-ℕ (nat-Fin x))
leq-nat-succ-Fin (succ-ℕ k) (inl x) =
  leq-eq-ℕ
    ( nat-Fin (skip-zero-Fin x))
    ( succ-ℕ (nat-Fin (inl x)))
    ( nat-skip-zero-Fin x)
leq-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-leq-ℕ
    ( succ-ℕ (nat-Fin (inr star)))
    ( is-zero-nat-zero-Fin {succ-ℕ k})
    ( leq-zero-ℕ (succ-ℕ (nat-Fin {succ-ℕ k} (inr star))))

leq-nat-mod-succ-ℕ :
  (k x : ℕ) → leq-ℕ (nat-Fin (mod-succ-ℕ k x)) x
leq-nat-mod-succ-ℕ k zero-ℕ =
  concatenate-eq-leq-ℕ zero-ℕ (is-zero-nat-zero-Fin {k}) (refl-leq-ℕ zero-ℕ)
leq-nat-mod-succ-ℕ k (succ-ℕ x) =
  transitive-leq-ℕ
    ( nat-Fin (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( leq-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x))
    ( leq-nat-mod-succ-ℕ k x)

-- Now we solve the exercise

euclidean-division-ℕ :
  (k x : ℕ) → Σ ℕ (λ r → (cong-ℕ k x r) × (is-nonzero-ℕ k → le-ℕ r k))
pr1 (euclidean-division-ℕ zero-ℕ x) = x
pr1 (pr2 (euclidean-division-ℕ zero-ℕ x)) = refl-cong-ℕ zero-ℕ x
pr2 (pr2 (euclidean-division-ℕ zero-ℕ x)) f = ex-falso (f refl)
pr1 (euclidean-division-ℕ (succ-ℕ k) x) = nat-Fin (mod-succ-ℕ k x)
pr1 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) =
  symm-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (mod-succ-ℕ k x))
    ( x)
    ( cong-nat-mod-succ-ℕ k x)
pr2 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) f =
  strict-upper-bound-nat-Fin (mod-succ-ℕ k x)

remainder-euclidean-division-ℕ : ℕ → ℕ → ℕ
remainder-euclidean-division-ℕ k x =
  pr1 (euclidean-division-ℕ k x)

cong-euclidean-division-ℕ :
  (k x : ℕ) → cong-ℕ k x (remainder-euclidean-division-ℕ k x)
cong-euclidean-division-ℕ k x =
  pr1 (pr2 (euclidean-division-ℕ k x))

strict-upper-bound-remainder-euclidean-division-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → le-ℕ (remainder-euclidean-division-ℕ k x) k
strict-upper-bound-remainder-euclidean-division-ℕ k x =
  pr2 (pr2 (euclidean-division-ℕ k x))

quotient-euclidean-division-ℕ : ℕ → ℕ → ℕ
quotient-euclidean-division-ℕ k x =
  pr1 (cong-euclidean-division-ℕ k x)

eq-quotient-euclidean-division-ℕ :
  (k x : ℕ) →
  Id ( mul-ℕ (quotient-euclidean-division-ℕ k x) k)
     ( dist-ℕ x (remainder-euclidean-division-ℕ k x))
eq-quotient-euclidean-division-ℕ k x =
  pr2 (cong-euclidean-division-ℕ k x)

eq-euclidean-division-ℕ :
  (k x : ℕ) →
  Id ( add-ℕ ( mul-ℕ (quotient-euclidean-division-ℕ k x) k)
             ( remainder-euclidean-division-ℕ k x))
     ( x)
eq-euclidean-division-ℕ zero-ℕ x =
  ( inv
    ( ap
      ( add-ℕ' x)
      ( right-zero-law-mul-ℕ (quotient-euclidean-division-ℕ zero-ℕ x)))) ∙
  ( left-unit-law-add-ℕ x)
eq-euclidean-division-ℕ (succ-ℕ k) x =
  ( ap ( add-ℕ' (remainder-euclidean-division-ℕ (succ-ℕ k) x))
       ( ( pr2 (cong-euclidean-division-ℕ (succ-ℕ k) x)) ∙
         ( symmetric-dist-ℕ x
           ( remainder-euclidean-division-ℕ (succ-ℕ k) x)))) ∙
  ( is-difference-dist-ℕ' (remainder-euclidean-division-ℕ (succ-ℕ k) x) x
    ( leq-nat-mod-succ-ℕ k x))

{- Exercise 7.10 -}

{- The type of k-ary natural numbers, for arbitrary k -}

data based-ℕ : ℕ → UU lzero where
  constant-based-ℕ : (k : ℕ) → Fin k → based-ℕ k
  unary-op-based-ℕ : (k : ℕ) → Fin k → based-ℕ k → based-ℕ k

{- Converting a k-ary natural number to a natural number -}

constant-ℕ : (k : ℕ) → Fin k → ℕ
constant-ℕ k x = nat-Fin x

unary-op-ℕ : (k : ℕ) → Fin k → ℕ → ℕ
unary-op-ℕ k x n = add-ℕ (mul-ℕ k (succ-ℕ n)) (nat-Fin x)

convert-based-ℕ : (k : ℕ) → based-ℕ k → ℕ
convert-based-ℕ k (constant-based-ℕ .k x) =
  constant-ℕ k x
convert-based-ℕ k (unary-op-based-ℕ .k x n) =
  unary-op-ℕ k x (convert-based-ℕ k n)

-- Exercise 7.10 (a)

{- The type of 0-ary natural numbers is empty -}
is-empty-based-zero-ℕ : is-empty (based-ℕ zero-ℕ)
is-empty-based-zero-ℕ (constant-based-ℕ .zero-ℕ ())
is-empty-based-zero-ℕ (unary-op-based-ℕ .zero-ℕ () n)

-- Exercise 7.10 (b)

{- We show that the function convert-based-ℕ is injective -}

cong-unary-op-ℕ :
  (k : ℕ) (x : Fin k) (n : ℕ) →
  cong-ℕ k (unary-op-ℕ k x n) (nat-Fin x)
cong-unary-op-ℕ (succ-ℕ k) x n =
  concatenate-cong-eq-ℕ
    ( succ-ℕ k)
    { unary-op-ℕ (succ-ℕ k) x n}
    ( translation-invariant-cong-ℕ'
      ( succ-ℕ k)
      ( mul-ℕ (succ-ℕ k) (succ-ℕ n))
      ( zero-ℕ)
      ( nat-Fin x)
      ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (succ-ℕ k))))
    ( left-unit-law-add-ℕ (nat-Fin x))

{- Any natural number of the form constant-ℕ k x is strictly less than any 
   natural number of the form unary-op-ℕ k y m -}

le-constant-unary-op-ℕ :
  (k : ℕ) (x y : Fin k) (m : ℕ) → le-ℕ (constant-ℕ k x) (unary-op-ℕ k y m)
le-constant-unary-op-ℕ k x y m =
  concatenate-le-leq-ℕ {nat-Fin x} {k} {unary-op-ℕ k y m}
    ( strict-upper-bound-nat-Fin x)
    ( transitive-leq-ℕ
      ( k)
      ( mul-ℕ k (succ-ℕ m))
      ( unary-op-ℕ k y m)
        ( leq-mul-ℕ m k)
        ( leq-add-ℕ (mul-ℕ k (succ-ℕ m)) (nat-Fin y)))

is-injective-convert-based-ℕ :
  (k : ℕ) → is-injective (convert-based-ℕ k)
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { constant-based-ℕ .(succ-ℕ k) x}
  { constant-based-ℕ .(succ-ℕ k) y} p =
  ap (constant-based-ℕ (succ-ℕ k)) (is-injective-nat-Fin p)
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { constant-based-ℕ .(succ-ℕ k) x}
  { unary-op-based-ℕ .(succ-ℕ k) y m} p =
  ex-falso
    ( neq-le-ℕ
      ( le-constant-unary-op-ℕ (succ-ℕ k) x y (convert-based-ℕ (succ-ℕ k) m))
      ( p))
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { unary-op-based-ℕ .(succ-ℕ k) x n}
  { constant-based-ℕ .(succ-ℕ k) y} p =
  ex-falso
    ( neq-le-ℕ
      ( le-constant-unary-op-ℕ (succ-ℕ k) y x (convert-based-ℕ (succ-ℕ k) n))
      ( inv p))
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { unary-op-based-ℕ .(succ-ℕ k) x n}
  { unary-op-based-ℕ .(succ-ℕ k) y m} p with
  -- the following term has type Id x y
  is-injective-nat-Fin {succ-ℕ k} {x} {y}
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin x)
      ( nat-Fin y)
      ( strict-upper-bound-nat-Fin x)
      ( strict-upper-bound-nat-Fin y)
      ( concatenate-cong-eq-cong-ℕ
        { succ-ℕ k}
        { nat-Fin x}
        { unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n)}
        { unary-op-ℕ (succ-ℕ k) y (convert-based-ℕ (succ-ℕ k) m)}
        { nat-Fin y}
        ( symm-cong-ℕ
          ( succ-ℕ k)
          ( unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n))
          ( nat-Fin x)
          ( cong-unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n)))
        ( p)
        ( cong-unary-op-ℕ (succ-ℕ k) y (convert-based-ℕ (succ-ℕ k) m))))
... | refl =
  ap ( unary-op-based-ℕ (succ-ℕ k) x)
     ( is-injective-convert-based-ℕ (succ-ℕ k)
       ( is-injective-succ-ℕ
         ( is-injective-mul-succ-ℕ k
           ( is-injective-add-ℕ' (nat-Fin x) p))))

-- Exercise 7.10 (c)
  
{- We show that the map convert-based-ℕ has an inverse. -}

-- The zero-element of the (k+1)-ary natural numbers
zero-based-ℕ : (k : ℕ) → based-ℕ (succ-ℕ k)
zero-based-ℕ k = constant-based-ℕ (succ-ℕ k) zero-Fin

-- The successor function on the k-ary natural numbers
succ-based-ℕ : (k : ℕ) → based-ℕ k → based-ℕ k
succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inl x)) =
  constant-based-ℕ (succ-ℕ k) (succ-Fin (inl x))
succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inr star)) =
  unary-op-based-ℕ (succ-ℕ k) zero-Fin (constant-based-ℕ (succ-ℕ k) zero-Fin)
succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inl x) n) =
  unary-op-based-ℕ (succ-ℕ k) (succ-Fin (inl x)) n
succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inr x) n) =
  unary-op-based-ℕ (succ-ℕ k) zero-Fin (succ-based-ℕ (succ-ℕ k) n)
  
-- The inverse map of convert-based-ℕ
inv-convert-based-ℕ : (k : ℕ) → ℕ → based-ℕ (succ-ℕ k)
inv-convert-based-ℕ k zero-ℕ =
  zero-based-ℕ k
inv-convert-based-ℕ k (succ-ℕ n) =
  succ-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ k n)

convert-based-succ-based-ℕ :
  (k : ℕ) (x : based-ℕ k) →
  Id (convert-based-ℕ k (succ-based-ℕ k x)) (succ-ℕ (convert-based-ℕ k x))
convert-based-succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inl x)) =
  nat-succ-Fin x
convert-based-succ-based-ℕ
  ( succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inr star)) =
  ( ap (λ t → add-ℕ (mul-ℕ (succ-ℕ k) (succ-ℕ t)) t) (is-zero-nat-zero-Fin {k})) ∙
  ( right-unit-law-mul-ℕ (succ-ℕ k))
convert-based-succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inl x) n) =
  ap ( add-ℕ (mul-ℕ (succ-ℕ k) (succ-ℕ (convert-based-ℕ (succ-ℕ k) n))))
     ( nat-succ-Fin {k} x)
convert-based-succ-based-ℕ
  (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inr star) n) =
  ( ap ( add-ℕ
         ( mul-ℕ
           ( succ-ℕ k)
           ( succ-ℕ (convert-based-ℕ (succ-ℕ k) (succ-based-ℕ (succ-ℕ k) n)))))
       ( is-zero-nat-zero-Fin {k})) ∙
  ( ( ap ( (mul-ℕ (succ-ℕ k)) ∘ succ-ℕ)
         ( convert-based-succ-based-ℕ (succ-ℕ k) n)) ∙
    ( ( right-successor-law-mul-ℕ
        ( succ-ℕ k)
        ( succ-ℕ (convert-based-ℕ (succ-ℕ k) n))) ∙
      ( commutative-add-ℕ
        ( succ-ℕ k)
        ( mul-ℕ (succ-ℕ k) (succ-ℕ (convert-based-ℕ (succ-ℕ k) n))))))
   
issec-inv-convert-based-ℕ :
  (k n : ℕ) → Id (convert-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ k n)) n
issec-inv-convert-based-ℕ k zero-ℕ = is-zero-nat-zero-Fin {k}
issec-inv-convert-based-ℕ k (succ-ℕ n) =
  ( convert-based-succ-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ  k n)) ∙
  ( ap succ-ℕ (issec-inv-convert-based-ℕ k n))

isretr-inv-convert-based-ℕ :
  (k : ℕ) (x : based-ℕ (succ-ℕ k)) →
  Id (inv-convert-based-ℕ k (convert-based-ℕ (succ-ℕ k) x)) x
isretr-inv-convert-based-ℕ k x =
  is-injective-convert-based-ℕ
    ( succ-ℕ k)
    ( issec-inv-convert-based-ℕ k (convert-based-ℕ (succ-ℕ k) x))

--------------------------------------------------------------------------------

map-extended-euclidean-algorithm : ℕ × ℕ → ℕ × ℕ
pr1 (map-extended-euclidean-algorithm (pair x y)) = y
pr2 (map-extended-euclidean-algorithm (pair x y)) =
  remainder-euclidean-division-ℕ y x

```
