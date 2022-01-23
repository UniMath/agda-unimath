---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.08-decidability-in-number-theory where

import foundations.07-modular-arithmetic
open foundations.07-modular-arithmetic public

--------------------------------------------------------------------------------

{- Section 8 Decidability in elementary number theory -}

--------------------------------------------------------------------------------

{- Section 8.1 Decidability and decidable equality -}

{- Definition 8.1.1 -}

is-decidable : {l : Level} (A : UU l) → UU l
is-decidable A = coprod A (¬ A)

is-decidable-fam :
  {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-fam {A = A} P = (x : A) → is-decidable (P x)

{- Example 8.1.2 -}

is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id

{- Example 8.1.3 -}

is-decidable-coprod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (coprod A B)
is-decidable-coprod (inl a) y = inl (inl a)
is-decidable-coprod (inr na) (inl b) = inl (inr b)
is-decidable-coprod (inr na) (inr nb) = inr (ind-coprod (λ x → empty) na nb)

is-decidable-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A × B)
is-decidable-prod (inl a) (inl b) = inl (pair a b)
is-decidable-prod (inl a) (inr g) = inr (g ∘ pr2)
is-decidable-prod (inr f) (inl b) = inr (f ∘ pr1)
is-decidable-prod (inr f) (inr g) = inr (f ∘ pr1)

is-decidable-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type (inl a) (inl b) = inl (λ x → b)
is-decidable-function-type (inl a) (inr g) = inr (λ h → g (h a))
is-decidable-function-type (inr f) (inl b) = inl (ex-falso ∘ f)
is-decidable-function-type (inr f) (inr g) = inl (ex-falso ∘ f)

is-decidable-neg :
  {l : Level} {A : UU l} → is-decidable A → is-decidable (¬ A)
is-decidable-neg d = is-decidable-function-type d is-decidable-empty

{- Example 8.1.4 -}

is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

is-decidable-leq-ℕ :
  (m n : ℕ) → is-decidable (leq-ℕ m n)
is-decidable-leq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-leq-ℕ m n

is-decidable-le-ℕ :
  (m n : ℕ) → is-decidable (le-ℕ m n)
is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n

{- Definition 8.1.5 -}

has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality A = (x y : A) → is-decidable (Id x y)

{- Proposition 8.1.6 -}

is-decidable-iff :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → (B → A) → is-decidable A → is-decidable B
is-decidable-iff f g =
  map-coprod f (functor-neg g)

{- Proposition 8.1.7 -}

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-eq-ℕ (is-decidable-Eq-ℕ x y)

-- We record some immediate corollaries

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

is-decidable-is-zero-ℕ' : (n : ℕ) → is-decidable (is-zero-ℕ' n)
is-decidable-is-zero-ℕ' n = has-decidable-equality-ℕ zero-ℕ n

is-decidable-is-nonzero-ℕ : (n : ℕ) → is-decidable (is-nonzero-ℕ n)
is-decidable-is-nonzero-ℕ n =
  is-decidable-neg (is-decidable-is-zero-ℕ n)

is-decidable-is-one-ℕ : (n : ℕ) → is-decidable (is-one-ℕ n)
is-decidable-is-one-ℕ n = has-decidable-equality-ℕ n one-ℕ

is-decidable-is-one-ℕ' : (n : ℕ) → is-decidable (is-one-ℕ' n)
is-decidable-is-one-ℕ' n = has-decidable-equality-ℕ one-ℕ n

is-decidable-is-not-one-ℕ :
  (x : ℕ) → is-decidable (is-not-one-ℕ x)
is-decidable-is-not-one-ℕ x =
  is-decidable-neg (is-decidable-is-one-ℕ x)

{- Proposition 8.1.8 -}

is-decidable-Eq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = inl star

has-decidable-equality-Fin :
  {k : ℕ} (x y : Fin k) → is-decidable (Id x y)
has-decidable-equality-Fin {k} x y =
  map-coprod eq-Eq-Fin (functor-neg Eq-Fin-eq) (is-decidable-Eq-Fin k x y)

is-decidable-is-zero-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-zero-Fin x)
is-decidable-is-zero-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin x zero-Fin

is-decidable-is-neg-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-neg-one-Fin x)
is-decidable-is-neg-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin x neg-one-Fin

is-decidable-is-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-one-Fin x)
is-decidable-is-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin x one-Fin

-- Bureaucracy

has-decidable-equality-empty : has-decidable-equality empty
has-decidable-equality-empty ()

has-decidable-equality-unit :
  has-decidable-equality unit
has-decidable-equality-unit star star = inl refl

{- Theorem 8.1.9 -}

is-decidable-div-ℕ : (d x : ℕ) → is-decidable (div-ℕ d x)
is-decidable-div-ℕ zero-ℕ x =
  is-decidable-iff
    ( div-eq-ℕ zero-ℕ x)
    ( inv ∘ (is-zero-div-zero-ℕ x))
    ( is-decidable-is-zero-ℕ' x)
is-decidable-div-ℕ (succ-ℕ d) x =
  is-decidable-iff
    ( div-is-zero-mod-succ-ℕ d x)
    ( is-zero-mod-succ-ℕ d x)
    ( is-decidable-is-zero-Fin (mod-succ-ℕ d x))

is-decidable-is-even-ℕ : (x : ℕ) → is-decidable (is-even-ℕ x)
is-decidable-is-even-ℕ x = is-decidable-div-ℕ two-ℕ x

is-decidable-is-odd-ℕ : (x : ℕ) → is-decidable (is-odd-ℕ x)
is-decidable-is-odd-ℕ x = is-decidable-neg (is-decidable-is-even-ℕ x)

--------------------------------------------------------------------------------

{- Section 8.2 Case analysis and definitions by with-abstraction -}

{- Definition 8.2.2 -}

collatz : ℕ → ℕ
collatz n with is-decidable-div-ℕ 2 n
... | inl (pair y p) = y
... | inr f = succ-ℕ (mul-ℕ 3 n)

{- Proposition 8.2.3 -}

is-decidable-function-type' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A → B)
is-decidable-function-type' (inl a) d with d a
... | inl b = inl (λ x → b)
... | inr nb = inr (λ f → nb (f a))
is-decidable-function-type' (inr na) d = inl (ex-falso ∘ na)

is-decidable-prod' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A × B)
is-decidable-prod' (inl a) d with d a
... | inl b = inl (pair a b)
... | inr nb = inr (nb ∘ pr2)
is-decidable-prod' (inr na) d = inr (na ∘ pr1)

{- Proposition 8.2.4 -}

-- There's a really cool application of with-abstraction here, on the recursive
-- call of the function itself!

is-decidable-Π-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (m : ℕ) →
  is-decidable ((x : ℕ) → (leq-ℕ m x) → P x) → is-decidable ((x : ℕ) → P x)
is-decidable-Π-ℕ P d zero-ℕ (inr nH) = inr (λ f → nH (λ x y → f x))
is-decidable-Π-ℕ P d zero-ℕ (inl H) = inl (λ x → H x (leq-zero-ℕ x))
is-decidable-Π-ℕ P d (succ-ℕ m) (inr nH) = inr (λ f → nH (λ x y → f x))
is-decidable-Π-ℕ P d (succ-ℕ m) (inl H) with d zero-ℕ
... | inr np = inr (λ f → np (f zero-ℕ))
... | inl p with
  is-decidable-Π-ℕ
    ( λ x → P (succ-ℕ x))
    ( λ x → d (succ-ℕ x))
    ( m)
    ( inl (λ x → H (succ-ℕ x)))
... | inl g = inl (ind-ℕ p (λ x y → g x))
... | inr ng = inr (λ f → ng (λ x → f (succ-ℕ x)))

{- Corollary 8.2.5 and some variations -}

is-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-upper-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ m n

is-strict-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-strict-upper-bound-ℕ P n =
  (m : ℕ) → P m → le-ℕ m n

is-upper-bound-is-strict-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-strict-upper-bound-ℕ P n → is-upper-bound-ℕ P n
is-upper-bound-is-strict-upper-bound-ℕ P n H x p =
  leq-le-ℕ {x} {n} (H x p)

is-decidable-bounded-Π-ℕ :
  {l1 l2 : Level} (P : ℕ → UU l1) (Q : ℕ → UU l2) (dP : is-decidable-fam P) →
  (dQ : is-decidable-fam Q) (m : ℕ) (H : is-upper-bound-ℕ P m) →
  is-decidable ((x : ℕ) → P x → Q x)
is-decidable-bounded-Π-ℕ P Q dP dQ m H =
  is-decidable-Π-ℕ
    ( λ x → P x → Q x)
    ( λ x → is-decidable-function-type (dP x) (dQ x))
    ( succ-ℕ m)
    ( inl (λ x l p → ex-falso (contradiction-leq-ℕ x m (H x p) l)))

is-decidable-bounded-Π-ℕ' :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (m : ℕ) →
  is-decidable ((x : ℕ) → (leq-ℕ x m) → P x)
is-decidable-bounded-Π-ℕ' P d m =
  is-decidable-bounded-Π-ℕ
    ( λ x → leq-ℕ x m)
    ( P)
    ( λ x → is-decidable-leq-ℕ x m)
    ( d)
    ( m)
    ( λ x → id)

is-decidable-strictly-bounded-Π-ℕ :
  {l1 l2 : Level} (P : ℕ → UU l1) (Q : ℕ → UU l2) (dP : is-decidable-fam P) →
  (dQ : is-decidable-fam Q) (m : ℕ) (H : is-strict-upper-bound-ℕ P m) →
  is-decidable ((x : ℕ) → P x → Q x)
is-decidable-strictly-bounded-Π-ℕ P Q dP dQ m H =
  is-decidable-bounded-Π-ℕ P Q dP dQ m (λ x p → leq-le-ℕ {x} {m} (H x p))

is-decidable-strictly-bounded-Π-ℕ' :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (m : ℕ) →
  is-decidable ((x : ℕ) → le-ℕ x m → P x)
is-decidable-strictly-bounded-Π-ℕ' P d m =
  is-decidable-strictly-bounded-Π-ℕ
    ( λ x → le-ℕ x m)
    ( P)
    ( λ x → is-decidable-le-ℕ x m)
    ( d)
    ( m)
    ( λ x → id)

--------------------------------------------------------------------------------

{- Section 8.3 The well-ordering principle of ℕ -}

{- Definition 8.3.2 -}

is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-lower-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ n m

{- Theorem 8.3.3 (The well-ordering principle of ℕ) -}

minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
minimal-element-ℕ P = Σ ℕ (λ n → (P n) × (is-lower-bound-ℕ P n))

is-minimal-element-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (m : ℕ) (pm : P (succ-ℕ m))
  (is-lower-bound-m : is-lower-bound-ℕ (λ x → P (succ-ℕ x)) m) →
  ¬ (P zero-ℕ) → is-lower-bound-ℕ P (succ-ℕ m)
is-minimal-element-succ-ℕ P d m pm is-lower-bound-m neg-p0 zero-ℕ p0 =
  ind-empty (neg-p0 p0)
is-minimal-element-succ-ℕ
  P d zero-ℕ pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  leq-zero-ℕ n
is-minimal-element-succ-ℕ
  P d (succ-ℕ m) pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  is-minimal-element-succ-ℕ (λ x → P (succ-ℕ x)) (λ x → d (succ-ℕ x)) m pm
    ( λ m → is-lower-bound-m (succ-ℕ m))
    ( is-lower-bound-m zero-ℕ)
    ( n)
    ( psuccn)

well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) →
  is-decidable (P zero-ℕ) →
  minimal-element-ℕ (λ m → P (succ-ℕ m)) → minimal-element-ℕ P
pr1 (well-ordering-principle-succ-ℕ P d n p (inl p0) _) = zero-ℕ
pr1 (pr2 (well-ordering-principle-succ-ℕ P d n p (inl p0) _)) = p0
pr2 (pr2 (well-ordering-principle-succ-ℕ P d n p (inl p0) _)) m q = leq-zero-ℕ m
pr1
  ( well-ordering-principle-succ-ℕ P d n p
    (inr neg-p0) (pair m (pair pm is-min-m))) = succ-ℕ m
pr1
  ( pr2
    ( well-ordering-principle-succ-ℕ P d n p
      (inr neg-p0) (pair m (pair pm is-min-m)))) = pm
pr2
  ( pr2
    ( well-ordering-principle-succ-ℕ P d n p
      (inr neg-p0) (pair m (pair pm is-min-m)))) =
  is-minimal-element-succ-ℕ P d m pm is-min-m neg-p0

well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  Σ ℕ P → minimal-element-ℕ P
pr1 (well-ordering-principle-ℕ P d (pair zero-ℕ p)) = zero-ℕ
pr1 (pr2 (well-ordering-principle-ℕ P d (pair zero-ℕ p))) = p
pr2 (pr2 (well-ordering-principle-ℕ P d (pair zero-ℕ p))) m q = leq-zero-ℕ m
well-ordering-principle-ℕ P d (pair (succ-ℕ n) p) =
  well-ordering-principle-succ-ℕ P d n p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ m → P (succ-ℕ m))
      ( λ m → d (succ-ℕ m))
      ( pair n p))

number-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (nP : Σ ℕ P) → ℕ
number-well-ordering-principle-ℕ P d nP =
  pr1 (well-ordering-principle-ℕ P d nP)

{- Also show that the well-ordering principle returns 0 if P 0 holds,
   independently of the input (pair n p) : Σ ℕ P. -}

is-zero-well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) (d0 : is-decidable (P zero-ℕ)) →
  (x : minimal-element-ℕ (λ m → P (succ-ℕ m))) (p0 : P zero-ℕ) →
  Id (pr1 (well-ordering-principle-succ-ℕ P d n p d0 x)) zero-ℕ
is-zero-well-ordering-principle-succ-ℕ P d n p (inl p0) x q0 =
  refl
is-zero-well-ordering-principle-succ-ℕ P d n p (inr np0) x q0 =
  ex-falso (np0 q0)

is-zero-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  (x : Σ ℕ P) → P zero-ℕ → Id (number-well-ordering-principle-ℕ P d x) zero-ℕ
is-zero-well-ordering-principle-ℕ P d (pair zero-ℕ p) p0 = refl
is-zero-well-ordering-principle-ℕ P d (pair (succ-ℕ m) p) =
  is-zero-well-ordering-principle-succ-ℕ P d m p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ z → P (succ-ℕ z))
      ( λ x → d (succ-ℕ x))
      ( pair m p))

--------------------------------------------------------------------------------

{- Section 8.4 The greatest common divisor -}

{- Definition 8.4.1 -}

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

leq-div-succ-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
leq-div-succ-ℕ d x (pair (succ-ℕ k) p) =
  concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p

leq-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → leq-ℕ d x
leq-div-ℕ d x f H with is-successor-is-nonzero-ℕ f
... | (pair y refl) = leq-div-succ-ℕ d y H

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
      ( ( α ∙ ( ap ( dist-ℕ a)
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

--------------------------------------------------------------------------------

{- Section 8.5 The infinitude of primes -}

{- Definition 8.5.1 -}

is-proper-divisor-ℕ : ℕ → ℕ → UU lzero
is-proper-divisor-ℕ n d = ¬ (Id d n) × div-ℕ d n

is-one-is-proper-divisor-ℕ : ℕ → UU lzero
is-one-is-proper-divisor-ℕ n =
  (x : ℕ) → is-proper-divisor-ℕ n x → is-one-ℕ x

is-prime-ℕ : ℕ → UU lzero
is-prime-ℕ n = (x : ℕ) → (is-proper-divisor-ℕ n x ↔ is-one-ℕ x)

{- Proposition 8.5.2 -}

is-prime-easy-ℕ : ℕ → UU lzero
is-prime-easy-ℕ n = (is-not-one-ℕ n) × (is-one-is-proper-divisor-ℕ n)

is-not-one-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-not-one-ℕ n
is-not-one-is-prime-ℕ n H p = pr1 (pr2 (H one-ℕ) refl) (inv p)

is-prime-easy-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-prime-easy-ℕ n
pr1 (is-prime-easy-is-prime-ℕ n H) = is-not-one-is-prime-ℕ n H
pr2 (is-prime-easy-is-prime-ℕ n H) x = pr1 (H x)

is-prime-is-prime-easy-ℕ : (n : ℕ) → is-prime-easy-ℕ n → is-prime-ℕ n
pr1 (is-prime-is-prime-easy-ℕ n H x) = pr2 H x
pr1 (pr2 (is-prime-is-prime-easy-ℕ n H .(succ-ℕ zero-ℕ)) refl) q = pr1 H (inv q)
pr2 (pr2 (is-prime-is-prime-easy-ℕ n H .(succ-ℕ zero-ℕ)) refl) = div-one-ℕ n

is-decidable-is-proper-divisor-ℕ :
  (n d : ℕ) → is-decidable (is-proper-divisor-ℕ n d)
is-decidable-is-proper-divisor-ℕ n d =
  is-decidable-prod
    ( is-decidable-neg (has-decidable-equality-ℕ d n))
    ( is-decidable-div-ℕ d n)

is-proper-divisor-zero-succ-ℕ : (n : ℕ) → is-proper-divisor-ℕ zero-ℕ (succ-ℕ n)
pr1 (is-proper-divisor-zero-succ-ℕ n) = Peano-8 n
pr2 (is-proper-divisor-zero-succ-ℕ n) = div-zero-ℕ (succ-ℕ n)

is-decidable-is-prime-easy-ℕ : (n : ℕ) → is-decidable (is-prime-easy-ℕ n)
is-decidable-is-prime-easy-ℕ zero-ℕ =
  inr
    ( λ H →
      is-not-one-two-ℕ (pr2 H two-ℕ (is-proper-divisor-zero-succ-ℕ one-ℕ)))
is-decidable-is-prime-easy-ℕ (succ-ℕ n) =
  is-decidable-prod
    ( is-decidable-neg (is-decidable-is-one-ℕ (succ-ℕ n)))
    ( is-decidable-bounded-Π-ℕ
      ( is-proper-divisor-ℕ (succ-ℕ n))
      ( is-one-ℕ)
      ( is-decidable-is-proper-divisor-ℕ (succ-ℕ n))
      ( is-decidable-is-one-ℕ)
      ( succ-ℕ n)
      ( λ x H → leq-div-succ-ℕ x n (pr2 H)))

is-decidable-is-prime-ℕ : (n : ℕ) → is-decidable (is-prime-ℕ n)
is-decidable-is-prime-ℕ n =
  is-decidable-iff
    ( is-prime-is-prime-easy-ℕ n)
    ( is-prime-easy-is-prime-ℕ n)
    ( is-decidable-is-prime-easy-ℕ n)

is-one-is-proper-divisor-two-ℕ : is-one-is-proper-divisor-ℕ two-ℕ
is-one-is-proper-divisor-two-ℕ zero-ℕ (pair f (pair k p)) =
  ex-falso (f (inv (right-zero-law-mul-ℕ k) ∙ p))
is-one-is-proper-divisor-two-ℕ (succ-ℕ zero-ℕ) (pair f H) = refl
is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) (pair f H) =
  ex-falso (f refl)
is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) (pair f H) =
  ex-falso (leq-div-succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) one-ℕ H)

is-prime-easy-two-ℕ : is-prime-easy-ℕ two-ℕ
pr1 is-prime-easy-two-ℕ = Eq-eq-ℕ
pr2 is-prime-easy-two-ℕ = is-one-is-proper-divisor-two-ℕ

is-prime-two-ℕ : is-prime-ℕ two-ℕ
is-prime-two-ℕ =
  is-prime-is-prime-easy-ℕ two-ℕ is-prime-easy-two-ℕ

{- Definition 8.5.3 -}

is-one-is-divisor-below-ℕ : ℕ → ℕ → UU lzero
is-one-is-divisor-below-ℕ n a =
  (x : ℕ) → leq-ℕ x n → div-ℕ x a → is-one-ℕ x

in-sieve-of-eratosthenes-ℕ : ℕ → ℕ → UU lzero
in-sieve-of-eratosthenes-ℕ n a =
  (le-ℕ n a) × (is-one-is-divisor-below-ℕ n a)

le-in-sieve-of-eratosthenes-ℕ :
  (n a : ℕ) → in-sieve-of-eratosthenes-ℕ n a → le-ℕ n a
le-in-sieve-of-eratosthenes-ℕ n a = pr1

{- Lemma 8.5.4 -}

is-decidable-in-sieve-of-eratosthenes-ℕ :
  (n a : ℕ) → is-decidable (in-sieve-of-eratosthenes-ℕ n a)
is-decidable-in-sieve-of-eratosthenes-ℕ n a =
  is-decidable-prod
    ( is-decidable-le-ℕ n a)
    ( is-decidable-bounded-Π-ℕ
      ( λ x → leq-ℕ x n)
      ( λ x → div-ℕ x a → is-one-ℕ x)
      ( λ x → is-decidable-leq-ℕ x n)
      ( λ x →
        is-decidable-function-type
          ( is-decidable-div-ℕ x a)
          ( is-decidable-is-one-ℕ x))
      ( n)
      ( λ x → id))

{- Lemma 8.5.5 -}

is-nonzero-factorial-ℕ :
  (x : ℕ) → is-nonzero-ℕ (factorial-ℕ x)
is-nonzero-factorial-ℕ zero-ℕ = Eq-eq-ℕ
is-nonzero-factorial-ℕ (succ-ℕ x) =
  is-nonzero-mul-ℕ
    ( factorial-ℕ x)
    ( succ-ℕ x)
    ( is-nonzero-factorial-ℕ x)
    ( Peano-8 x)

leq-factorial-ℕ :
  (n : ℕ) → leq-ℕ n (factorial-ℕ n)
leq-factorial-ℕ zero-ℕ = leq-zero-ℕ one-ℕ
leq-factorial-ℕ (succ-ℕ n) =
  leq-mul-is-nonzero-ℕ'
    ( factorial-ℕ n)
    ( succ-ℕ n)
    ( is-nonzero-factorial-ℕ n)

in-sieve-of-eratosthenes-succ-factorial-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (succ-ℕ (factorial-ℕ n))
pr1 (in-sieve-of-eratosthenes-succ-factorial-ℕ zero-ℕ) = star
pr2 (in-sieve-of-eratosthenes-succ-factorial-ℕ zero-ℕ) x l d =
  ex-falso
    ( Eq-eq-ℕ
      ( is-zero-is-zero-div-ℕ x two-ℕ d (is-zero-leq-zero-ℕ x l)))
pr1 (in-sieve-of-eratosthenes-succ-factorial-ℕ (succ-ℕ n)) =
  concatenate-leq-le-ℕ
    { succ-ℕ n}
    { factorial-ℕ (succ-ℕ n)}
    { succ-ℕ (factorial-ℕ (succ-ℕ n))}
    ( leq-factorial-ℕ (succ-ℕ n))
    ( le-succ-ℕ {factorial-ℕ (succ-ℕ n)})
pr2 (in-sieve-of-eratosthenes-succ-factorial-ℕ (succ-ℕ n)) x l (pair y p) with
  is-decidable-is-zero-ℕ x
... | inl refl =
  ex-falso
    ( Peano-8
      ( factorial-ℕ (succ-ℕ n))
      ( inv p ∙ (right-zero-law-mul-ℕ y)))
... | inr f =
  is-one-div-ℕ x
    ( factorial-ℕ (succ-ℕ n))
    ( div-factorial-is-nonzero-ℕ (succ-ℕ n) x l f)
    ( pair y p)

{- Theorem 8.5.6 The infinitude of primes -}

minimal-element-in-sieve-of-eratosthenes-ℕ :
  (n : ℕ) → minimal-element-ℕ (in-sieve-of-eratosthenes-ℕ n)
minimal-element-in-sieve-of-eratosthenes-ℕ n =
  well-ordering-principle-ℕ
    ( in-sieve-of-eratosthenes-ℕ n)
    ( is-decidable-in-sieve-of-eratosthenes-ℕ n)
    ( pair
      ( succ-ℕ (factorial-ℕ n))
      ( in-sieve-of-eratosthenes-succ-factorial-ℕ n))

larger-prime-ℕ : ℕ → ℕ
larger-prime-ℕ n = pr1 (minimal-element-in-sieve-of-eratosthenes-ℕ n)

in-sieve-of-eratosthenes-larger-prime-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (larger-prime-ℕ n)
in-sieve-of-eratosthenes-larger-prime-ℕ n =
  pr1 (pr2 (minimal-element-in-sieve-of-eratosthenes-ℕ n))

is-one-is-divisor-below-larger-prime-ℕ :
  (n : ℕ) → is-one-is-divisor-below-ℕ n (larger-prime-ℕ n)
is-one-is-divisor-below-larger-prime-ℕ n =
  pr2 (in-sieve-of-eratosthenes-larger-prime-ℕ n)

le-larger-prime-ℕ : (n : ℕ) → le-ℕ n (larger-prime-ℕ n)
le-larger-prime-ℕ n = pr1 (in-sieve-of-eratosthenes-larger-prime-ℕ n)

is-nonzero-larger-prime-ℕ : (n : ℕ) → is-nonzero-ℕ (larger-prime-ℕ n)
is-nonzero-larger-prime-ℕ n =
  is-nonzero-le-ℕ n (larger-prime-ℕ n) (le-larger-prime-ℕ n)

is-lower-bound-larger-prime-ℕ :
  (n : ℕ) → is-lower-bound-ℕ (in-sieve-of-eratosthenes-ℕ n) (larger-prime-ℕ n)
is-lower-bound-larger-prime-ℕ n =
  pr2 (pr2 (minimal-element-in-sieve-of-eratosthenes-ℕ n))

is-not-one-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-not-one-ℕ (larger-prime-ℕ n)
is-not-one-larger-prime-ℕ n H p with is-successor-is-nonzero-ℕ H
... | pair k refl =
  neq-le-ℕ {one-ℕ} {larger-prime-ℕ n}
    ( concatenate-leq-le-ℕ {one-ℕ} {succ-ℕ k} {larger-prime-ℕ n} star
      ( le-larger-prime-ℕ (succ-ℕ k)))
    ( inv p)

neg-left-factor-neg-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → ¬ (A × B) → B → ¬ A
neg-left-factor-neg-prod f b a = f (pair a b)

neg-right-factor-neg-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → ¬ (A × B) → A → ¬ B
neg-right-factor-neg-prod f a b = f (pair a b)

le-is-proper-divisor-ℕ :
  (x y : ℕ) → is-nonzero-ℕ y → is-proper-divisor-ℕ y x → le-ℕ x y
le-is-proper-divisor-ℕ x y H K =
  le-leq-neq-ℕ (leq-div-ℕ x y H (pr2 K)) (pr1 K)

not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ :
  (n x : ℕ) → is-proper-divisor-ℕ (larger-prime-ℕ n) x →
  ¬ (in-sieve-of-eratosthenes-ℕ n x)
not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x H K =
  ex-falso
    ( contradiction-le-ℕ x (larger-prime-ℕ n)
      ( le-is-proper-divisor-ℕ x (larger-prime-ℕ n)
        ( is-nonzero-larger-prime-ℕ n)
        ( H))
      ( is-lower-bound-larger-prime-ℕ n x K))

is-one-is-proper-divisor-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-one-is-proper-divisor-ℕ (larger-prime-ℕ n)
is-one-is-proper-divisor-larger-prime-ℕ n H x (pair f K) =
  is-one-is-divisor-below-larger-prime-ℕ n x
    ( leq-not-le-ℕ n x
      ( neg-left-factor-neg-prod
        ( not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x
          ( pair f K))
        ( λ y l d →
          is-one-is-divisor-below-larger-prime-ℕ n y l
            ( transitive-div-ℕ y x (larger-prime-ℕ n) d K))))
    ( K)

is-prime-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-prime-ℕ (larger-prime-ℕ n)
is-prime-larger-prime-ℕ n H =
  is-prime-is-prime-easy-ℕ
    ( larger-prime-ℕ n)
    ( pair
      ( is-not-one-larger-prime-ℕ n H)
      ( is-one-is-proper-divisor-larger-prime-ℕ n H))

infinitude-of-primes-ℕ :
  (n : ℕ) → Σ ℕ (λ p → is-prime-ℕ p × le-ℕ n p)
infinitude-of-primes-ℕ n with is-decidable-is-zero-ℕ n
... | inl refl = pair two-ℕ (pair is-prime-two-ℕ star)
... | inr H =
  pair
    ( larger-prime-ℕ n)
    ( pair
      ( is-prime-larger-prime-ℕ n H)
      ( le-larger-prime-ℕ n))

--------------------------------------------------------------------------------

{- Section 8.6 Boolean reflection -}

{- Definition 8.6.1 -}

booleanization : {l : Level} {A : UU l} → is-decidable A → bool
booleanization (inl a) = true
booleanization (inr f) = false

{- Proposition 8.6.2 -}

inv-boolean-reflection :
  {l : Level} {A : UU l} (d : is-decidable A) → A → Id (booleanization d) true
inv-boolean-reflection (inl a) x = refl
inv-boolean-reflection (inr f) x = ex-falso (f x)

boolean-reflection :
  {l : Level} {A : UU l} (d : is-decidable A) → Id (booleanization d) true → A
boolean-reflection (inl a) p = a
boolean-reflection (inr f) p = ex-falso (Eq-eq-bool p)

{-
four-hundred-and-nine-ℕ : ℕ
four-hundred-and-nine-ℕ = add-ℕ (mul-ℕ 20 20) nine-ℕ

is-prime-four-hundred-and-nine-ℕ : is-prime-ℕ four-hundred-and-nine-ℕ
is-prime-four-hundred-and-nine-ℕ =
  boolean-reflection
    ( is-decidable-is-prime-ℕ four-hundred-and-nine-ℕ)
    ( refl)
-}

--------------------------------------------------------------------------------

{- Exercises -}

--------------------------------------------------------------------------------

{- Exercise 8.1 -}

{- The Goldbach conjecture asserts that every even number above 2 is the sum
   of two primes. -}

Goldbach-conjecture : UU lzero
Goldbach-conjecture =
  ( n : ℕ) → (le-ℕ two-ℕ n) → (is-even-ℕ n) →
    Σ ℕ (λ p → (is-prime-ℕ p) × (Σ ℕ (λ q → (is-prime-ℕ q) × Id (add-ℕ p q) n)))

is-twin-prime-ℕ : ℕ → UU lzero
is-twin-prime-ℕ n = (is-prime-ℕ n) × (is-prime-ℕ (succ-ℕ (succ-ℕ n)))

{- The twin prime conjecture asserts that there are infinitely many twin
   primes. We assert that there are infinitely twin primes by asserting that
   for every n : ℕ there is a twin prime that is larger than n. -}

Twin-prime-conjecture : UU lzero
Twin-prime-conjecture =
  (n : ℕ) → Σ ℕ (λ p → (is-twin-prime-ℕ p) × (leq-ℕ n p))

iterate-collatz : ℕ → ℕ → ℕ
iterate-collatz zero-ℕ n = n
iterate-collatz (succ-ℕ k) n =
  collatz (iterate-collatz k n)

Collatz-conjecture : UU lzero
Collatz-conjecture =
  (n : ℕ) →
  is-nonzero-ℕ n → Σ ℕ (λ k → Id (iterate-collatz k n) one-ℕ)

--------------------------------------------------------------------------------

{- Exercise 8.2 -}

idempotent-is-decidable :
  {l : Level} (P : UU l) → is-decidable (is-decidable P) → is-decidable P
idempotent-is-decidable P =
  map-right-unit-law-coprod-is-empty
    ( is-decidable P)
    ( ¬ (is-decidable P))
    ( dn-is-decidable)

{- Exercise 8.3 -}

exists-not-not-forall-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} → (is-decidable-fam P) →
  ¬ ((x : Fin k) → P x) → Σ (Fin k) (λ x → ¬ (P x))
exists-not-not-forall-Fin {l} {zero-ℕ} d H = ex-falso (H ind-empty)
exists-not-not-forall-Fin {l} {succ-ℕ k} {P} d H with d (inr star)
... | inl p =
  T ( exists-not-not-forall-Fin
      ( λ x → d (inl x))
      ( λ f → H (ind-coprod P f (ind-unit p))))
  where
  T : Σ (Fin k) (λ x → ¬ (P (inl x))) → Σ (Fin (succ-ℕ k)) (λ x → ¬ (P x))
  T z = pair (inl (pr1 z)) (pr2 z)
... | inr f = pair (inr star) f

{- Exercise 8.4 -}

-- Exercise 8.4 (a)

prime-ℕ : ℕ → ℕ
prime-ℕ zero-ℕ = two-ℕ
prime-ℕ (succ-ℕ n) = pr1 (infinitude-of-primes-ℕ (prime-ℕ n))

-- Exercise 8.4 (b)

prime-counting-ℕ : ℕ → ℕ
prime-counting-ℕ zero-ℕ = zero-ℕ
prime-counting-ℕ (succ-ℕ n) with is-decidable-is-prime-ℕ (succ-ℕ n)
... | inl x = succ-ℕ (prime-counting-ℕ n)
... | inr x = prime-counting-ℕ n

--------------------------------------------------------------------------------

{- Exercise 8.5 -}

--------------------------------------------------------------------------------

{- Exercise 8.6 -}

has-decidable-equality-prod' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (f : B → has-decidable-equality A) (g : A → has-decidable-equality B) →
  has-decidable-equality (A × B)
has-decidable-equality-prod' f g (pair x y) (pair x' y') with
  f y x x' | g x y y'
... | inl refl | inl refl = inl refl
... | inl refl | inr nq = inr (λ r → nq (ap pr2 r))
... | inr np | inl refl = inr (λ r → np (ap pr1 r))
... | inr np | inr nq = inr (λ r → np (ap pr1 r))

has-decidable-equality-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality A → has-decidable-equality B →
  has-decidable-equality (A × B)
has-decidable-equality-prod d e =
  has-decidable-equality-prod' (λ y → d) (λ x → e)

has-decidable-equality-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → B → has-decidable-equality A
has-decidable-equality-left-factor d b x y with d (pair x b) (pair y b)
... | inl p = inl (ap pr1 p)
... | inr np = inr (λ q → np (ap (λ z → pair z b) q))

has-decidable-equality-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → A → has-decidable-equality B
has-decidable-equality-right-factor d a x y with d (pair a x) (pair a y)
... | inl p = inl (ap pr2 p)
... | inr np = inr (λ q → np (ap (pair a) q))

--------------------------------------------------------------------------------

{- Exercise 8.7 -}

-- We define observational equality of coproducts.

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  data Eq-coprod : coprod A B → coprod A B → UU (l1 ⊔ l2)
    where
    Eq-eq-coprod-inl : {x y : A} → Id x y → Eq-coprod (inl x) (inl y)
    Eq-eq-coprod-inr : {x y : B} → Id x y → Eq-coprod (inr x) (inr y)

  -- Exercise 8.7 (a)

  refl-Eq-coprod : (x : coprod A B) → Eq-coprod x x
  refl-Eq-coprod (inl x) = Eq-eq-coprod-inl refl
  refl-Eq-coprod (inr x) = Eq-eq-coprod-inr refl

  Eq-eq-coprod : (x y : coprod A B) → Id x y → Eq-coprod x y
  Eq-eq-coprod x .x refl = refl-Eq-coprod x

  eq-Eq-coprod : (x y : coprod A B) → Eq-coprod x y → Id x y
  eq-Eq-coprod .(inl x) .(inl x) (Eq-eq-coprod-inl {x} {.x} refl) = refl
  eq-Eq-coprod .(inr x) .(inr x) (Eq-eq-coprod-inr {x} {.x} refl) = refl

  is-injective-inl : is-injective {B = coprod A B} inl
  is-injective-inl refl = refl

  is-injective-inr : is-injective {B = coprod A B} inr
  is-injective-inr refl = refl 

  neq-inl-inr :
    (x : A) (y : B) → ¬ (Id (inl x) (inr y))
  neq-inl-inr x y ()

  neq-inr-inl :
    (x : B) (y : A) → ¬ (Id (inr x) (inl y))
  neq-inr-inl x y ()
  
  -- Exercise 8.7 (b)

  has-decidable-equality-coprod :
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (coprod A B)
  has-decidable-equality-coprod d e (inl x) (inl y) =
    is-decidable-iff (ap inl) is-injective-inl (d x y)
  has-decidable-equality-coprod d e (inl x) (inr y) =
    inr (neq-inl-inr x y)
  has-decidable-equality-coprod d e (inr x) (inl y) =
    inr (neq-inr-inl x y)
  has-decidable-equality-coprod d e (inr x) (inr y) =
    is-decidable-iff (ap inr) is-injective-inr (e x y)

  has-decidable-equality-left-summand :
    has-decidable-equality (coprod A B) → has-decidable-equality A
  has-decidable-equality-left-summand d x y =
    is-decidable-iff is-injective-inl (ap inl) (d (inl x) (inl y))

  has-decidable-equality-right-summand :
    has-decidable-equality (coprod A B) → has-decidable-equality B
  has-decidable-equality-right-summand d x y =
    is-decidable-iff is-injective-inr (ap inr) (d (inr x) (inr y))

has-decidable-equality-ℤ : has-decidable-equality ℤ
has-decidable-equality-ℤ =
  has-decidable-equality-coprod
    has-decidable-equality-ℕ
    ( has-decidable-equality-coprod
      has-decidable-equality-unit
      has-decidable-equality-ℕ)

is-decidable-is-zero-ℤ :
  (x : ℤ) → is-decidable (is-zero-ℤ x)
is-decidable-is-zero-ℤ x = has-decidable-equality-ℤ x zero-ℤ

is-decidable-is-one-ℤ :
  (x : ℤ) → is-decidable (is-one-ℤ x)
is-decidable-is-one-ℤ x = has-decidable-equality-ℤ x one-ℤ

is-decidable-is-neg-one-ℤ :
  (x : ℤ) → is-decidable (is-neg-one-ℤ x)
is-decidable-is-neg-one-ℤ x = has-decidable-equality-ℤ x neg-one-ℤ

--------------------------------------------------------------------------------

{- Exercise 8.8 -}

--------------------------------------------------------------------------------

{- Exercise 8.9 -}

--------------------------------------------------------------------------------

{- Exercise 8.10 -}

-- Exercise 8.10 (a)

-- Decidability of bounded Σ-types

is-decidable-Σ-ℕ :
  {l : Level} (m : ℕ) (P : ℕ → UU l) (d : is-decidable-fam P) →
  is-decidable (Σ ℕ (λ x → (leq-ℕ m x) × (P x))) → is-decidable (Σ ℕ P)
is-decidable-Σ-ℕ m P d (inl (pair x (pair l p))) = inl (pair x p)
is-decidable-Σ-ℕ zero-ℕ P d (inr f) =
  inr (λ p → f (pair (pr1 p) (pair star (pr2 p))))
is-decidable-Σ-ℕ (succ-ℕ m) P d (inr f) with d zero-ℕ
... | inl p = inl (pair zero-ℕ p)
... | inr g with
  is-decidable-Σ-ℕ m
    ( P ∘ succ-ℕ)
    ( λ x → d (succ-ℕ x))
    ( inr (λ p → f (pair (succ-ℕ (pr1 p)) (pr2 p))))
... | inl p = inl (pair (succ-ℕ (pr1 p)) (pr2 p))
... | inr h = inr α
  where
  α : Σ ℕ P → empty
  α (pair zero-ℕ p) = g p
  α (pair (succ-ℕ x) p) = h (pair x p)

is-decidable-bounded-Σ-ℕ :
  {l1 l2 : Level} (m : ℕ) (P : ℕ → UU l1) (Q : ℕ → UU l2)
  (dP : is-decidable-fam P) (dQ : is-decidable-fam Q)
  (H : is-upper-bound-ℕ P m) → is-decidable (Σ ℕ (λ x → (P x) × (Q x)))
is-decidable-bounded-Σ-ℕ m P Q dP dQ H =
  is-decidable-Σ-ℕ
    ( succ-ℕ m)
    ( λ x → (P x) × (Q x))
    ( λ x → is-decidable-prod (dP x) (dQ x))
    ( inr
      ( λ p →
        contradiction-leq-ℕ
          ( pr1 p)
          ( m)
          ( H (pr1 p) (pr1 (pr2 (pr2 p))))
          ( pr1 (pr2 p))))

is-decidable-bounded-Σ-ℕ' :
  {l : Level} (m : ℕ) (P : ℕ → UU l) (d : is-decidable-fam P) →
  is-decidable (Σ ℕ (λ x → (leq-ℕ x m) × (P x)))
is-decidable-bounded-Σ-ℕ' m P d =
  is-decidable-bounded-Σ-ℕ m
    ( λ x → leq-ℕ x m)
    ( P)
    ( λ x → is-decidable-leq-ℕ x m)
    ( d)
    ( λ x → id)

is-decidable-strictly-bounded-Σ-ℕ :
  {l1 l2 : Level} (m : ℕ) (P : ℕ → UU l1) (Q : ℕ → UU l2)
  (dP : is-decidable-fam P) (dQ : is-decidable-fam Q)
  (H : is-strict-upper-bound-ℕ P m) →
  is-decidable (Σ ℕ (λ x → (P x) × (Q x)))
is-decidable-strictly-bounded-Σ-ℕ m P Q dP dQ H =
  is-decidable-bounded-Σ-ℕ m P Q dP dQ
    ( is-upper-bound-is-strict-upper-bound-ℕ P m H)

is-decidable-strictly-bounded-Σ-ℕ' :
  {l : Level} (m : ℕ) (P : ℕ → UU l) (d : is-decidable-fam P) →
  is-decidable (Σ ℕ (λ x → (le-ℕ x m) × (P x)))
is-decidable-strictly-bounded-Σ-ℕ' m P d =
  is-decidable-strictly-bounded-Σ-ℕ m
    ( λ x → le-ℕ x m)
    ( P)
    ( λ x → is-decidable-le-ℕ x m)
    ( d)
    ( λ x → id)

--------------------------------------------------------------------------------

{- Exercise 8.11 -}

-- Before we solve the exercise we introduce divisibility in Fin k
-- The exercise can also be solved more directly

div-Fin : {k : ℕ} → Fin k → Fin k → UU lzero
div-Fin {k} x y = Σ (Fin k) (λ u → Id (mul-Fin u x) y)

refl-div-Fin : {k : ℕ} (x : Fin k) → div-Fin x x
pr1 (refl-div-Fin {succ-ℕ k} x) = one-Fin
pr2 (refl-div-Fin {succ-ℕ k} x) = left-unit-law-mul-Fin x

trans-div-Fin :
  {k : ℕ} (x y z : Fin k) → div-Fin x y → div-Fin y z → div-Fin x z
pr1 (trans-div-Fin x y z (pair u p) (pair v q)) = mul-Fin v u
pr2 (trans-div-Fin x y z (pair u p) (pair v q)) =
  associative-mul-Fin v u x ∙ (ap (mul-Fin v) p ∙ q)

div-zero-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin x zero-Fin
pr1 (div-zero-Fin x) = zero-Fin
pr2 (div-zero-Fin x) = left-zero-law-mul-Fin x

div-one-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin one-Fin x
pr1 (div-one-Fin x) = x
pr2 (div-one-Fin x) = right-unit-law-mul-Fin x

is-zero-div-zero-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin zero-Fin x → is-zero-Fin x
is-zero-div-zero-Fin {k} x (pair u p) = inv p ∙ right-zero-law-mul-Fin u

is-unit-Fin : {k : ℕ} → Fin k → UU lzero
is-unit-Fin {succ-ℕ k} x = div-Fin x one-Fin

unit-Fin : ℕ → UU lzero
unit-Fin k = Σ (Fin k) is-unit-Fin

is-unit-one-Fin : {k : ℕ} → is-unit-Fin (one-Fin {k})
is-unit-one-Fin {k} = refl-div-Fin one-Fin

one-unit-Fin : {k : ℕ} → unit-Fin (succ-ℕ k)
pr1 (one-unit-Fin {k}) = one-Fin
pr2 (one-unit-Fin {k}) = is-unit-one-Fin

is-unit-neg-one-Fin : {k : ℕ} → is-unit-Fin (neg-one-Fin {k})
is-unit-neg-one-Fin {zero-ℕ} = refl-div-Fin neg-one-Fin
pr1 (is-unit-neg-one-Fin {succ-ℕ k}) = neg-one-Fin
pr2 (is-unit-neg-one-Fin {succ-ℕ k}) =
  eq-mod-succ-cong-ℕ
    ( succ-ℕ k)
    ( mul-ℕ (succ-ℕ k) (succ-ℕ k))
    ( one-ℕ)
    ( concatenate-eq-cong-ℕ
      ( succ-ℕ (succ-ℕ k))
      { x3 = one-ℕ}
      ( square-succ-ℕ k)
      ( pair k
        ( ( commutative-mul-ℕ k (succ-ℕ (succ-ℕ k))) ∙
          ( inv (right-unit-law-dist-ℕ (mul-ℕ (succ-ℕ (succ-ℕ k)) k))))))

neg-one-unit-Fin : {k : ℕ} → unit-Fin (succ-ℕ k)
pr1 neg-one-unit-Fin = neg-one-Fin
pr2 neg-one-unit-Fin = is-unit-neg-one-Fin

is-unit-mul-Fin :
  {k : ℕ} {x y : Fin k} →
  is-unit-Fin x → is-unit-Fin y → is-unit-Fin (mul-Fin x y)
pr1 (is-unit-mul-Fin {succ-ℕ k} {x} {y} (pair d p) (pair e q)) = mul-Fin e d
pr2 (is-unit-mul-Fin {succ-ℕ k} {x} {y} (pair d p) (pair e q)) =
  ( associative-mul-Fin e d (mul-Fin x y)) ∙
    ( ( ap
        ( mul-Fin e)
        ( ( inv (associative-mul-Fin d x y)) ∙
          ( ap (mul-Fin' y) p ∙ left-unit-law-mul-Fin y))) ∙
      ( q))

mul-unit-Fin : {k : ℕ} → unit-Fin k → unit-Fin k → unit-Fin k
pr1 (mul-unit-Fin u v) = mul-Fin (pr1 u) (pr1 v)
pr2 (mul-unit-Fin u v) = is-unit-mul-Fin (pr2 u) (pr2 v)

inv-unit-Fin : {k : ℕ} → unit-Fin k → unit-Fin k
pr1 (inv-unit-Fin {succ-ℕ k} (pair u (pair v p))) = v
pr1 (pr2 (inv-unit-Fin {succ-ℕ k} (pair u (pair v p)))) = u
pr2 (pr2 (inv-unit-Fin {succ-ℕ k} (pair u (pair v p)))) =
  commutative-mul-Fin u v ∙ p

sim-unit-Fin :
  {k : ℕ} → Fin k → Fin k → UU lzero
sim-unit-Fin {k} x y = Σ (unit-Fin k) (λ u → Id (mul-Fin (pr1 u) x) y)

refl-sim-unit-Fin :
  {k : ℕ} (x : Fin k) → sim-unit-Fin x x
pr1 (refl-sim-unit-Fin {succ-ℕ k} x) = one-unit-Fin
pr2 (refl-sim-unit-Fin {succ-ℕ k} x) = left-unit-law-mul-Fin x

symm-sim-unit-Fin :
  {k : ℕ} (x y : Fin k) → sim-unit-Fin x y → sim-unit-Fin y x
pr1 (symm-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p)) =
  inv-unit-Fin (pair u (pair v q))
pr2 (symm-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p)) =
  ( ( ( ap (mul-Fin v) (inv p)) ∙
        ( inv (associative-mul-Fin v u x))) ∙
      ( ap (mul-Fin' x) q)) ∙
    ( left-unit-law-mul-Fin x)

trans-sim-unit-Fin :
  {k : ℕ} (x y z : Fin k) → sim-unit-Fin x y → sim-unit-Fin y z →
  sim-unit-Fin x z
pr1 (trans-sim-unit-Fin {succ-ℕ k} x y z (pair u p) (pair v q)) =
  mul-unit-Fin v u
pr2 (trans-sim-unit-Fin {succ-ℕ k} x y z (pair u p) (pair v q)) =
  associative-mul-Fin (pr1 v) (pr1 u) x ∙ (ap (mul-Fin (pr1 v)) p ∙ q)

is-mod-unit-ℕ : (k x : ℕ) → UU lzero
is-mod-unit-ℕ k x = Σ ℕ (λ l → cong-ℕ k (mul-ℕ l x) one-ℕ)

is-mod-unit-sim-unit-mod-succ-ℕ :
  (k x : ℕ) → sim-unit-Fin (mod-succ-ℕ k x) one-Fin → is-mod-unit-ℕ (succ-ℕ k) x
pr1 (is-mod-unit-sim-unit-mod-succ-ℕ k x (pair u p)) =
  nat-Fin (pr1 u)
pr2 (is-mod-unit-sim-unit-mod-succ-ℕ k x (pair u p)) =
  cong-eq-mod-succ-ℕ k
    ( mul-ℕ (nat-Fin (pr1 u)) x)
    ( one-ℕ)
    ( ( eq-mod-succ-cong-ℕ k
        ( mul-ℕ (nat-Fin (pr1 u)) x)
        ( mul-ℕ (nat-Fin (pr1 u)) (nat-Fin (mod-succ-ℕ k x)))
        ( scalar-invariant-cong-ℕ
          ( succ-ℕ k)
          ( x)
          ( nat-Fin (mod-succ-ℕ k x))
          ( nat-Fin (pr1 u))
          ( symm-cong-ℕ
            ( succ-ℕ k)
            ( nat-Fin (mod-succ-ℕ k x))
            ( x)
            ( cong-nat-mod-succ-ℕ k x)))) ∙
      ( p))

-- We now come back to the solution of the exercise

is-decidable-Σ-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} →
  ((x : Fin k) → is-decidable (P x)) → is-decidable (Σ (Fin k) P)
is-decidable-Σ-Fin {l} {zero-ℕ} {P} d = inr pr1
is-decidable-Σ-Fin {l} {succ-ℕ k} {P} d with d (inr star)
... | inl p = inl (pair (inr star) p)
... | inr f =
  is-decidable-iff
    ( λ t → pair (inl (pr1 t)) (pr2 t))
    ( g)
    ( is-decidable-Σ-Fin {l} {k} {P ∘ inl} (λ x → d (inl x)))
  where
  g : Σ (Fin (succ-ℕ k)) P → Σ (Fin k) (P ∘ inl)
  g (pair (inl x) p) = pair x p
  g (pair (inr star) p) = ex-falso (f p)

is-decidable-div-Fin : {k : ℕ} (x y : Fin k) → is-decidable (div-Fin x y)
is-decidable-div-Fin x y =
  is-decidable-Σ-Fin (λ u → has-decidable-equality-Fin (mul-Fin u x) y)

is-linear-combination-dist-ℕ : ℕ → ℕ → ℕ → UU lzero
is-linear-combination-dist-ℕ x y z =
  Σ ℕ (λ k → Σ ℕ (λ l → Id (dist-ℕ (mul-ℕ k x) (mul-ℕ l y)) z))

{-
sim-unit-dist-ℕ :
  (k x y : ℕ) →
  sim-unit-Fin (mod-succ-ℕ x (dist-ℕ (mul-ℕ k (succ-ℕ x)) y)) (mod-succ-ℕ x y)
sim-unit-dist-ℕ k x y = {!decide-leq-ℕ!}
  where
  f : coprod (mul-ℕ k (succ-ℕ x) ≤-ℕ y) (y ≤-ℕ mul-ℕ k (succ-ℕ x)) →
      sim-unit-Fin
        ( mod-succ-ℕ x (dist-ℕ (mul-ℕ k (succ-ℕ x)) y))
        ( mod-succ-ℕ x y)
  f (inl H) =
    pair
      ( one-unit-Fin)
      ( ( left-unit-law-mul-Fin
          ( mod-succ-ℕ x (dist-ℕ (mul-ℕ k (succ-ℕ x)) y))) ∙
        ( eq-mod-succ-cong-ℕ x
          ( dist-ℕ (mul-ℕ k (succ-ℕ x)) y)
          ( y)
          ( concatenate-eq-cong-eq-ℕ
            ( succ-ℕ x)
            ( inv (left-unit-law-add-ℕ (dist-ℕ (mul-ℕ k (succ-ℕ x)) y)))
            ( translation-invariant-cong-ℕ'
              ( succ-ℕ x)
              ( zero-ℕ)
              ( mul-ℕ k (succ-ℕ x))
              ( dist-ℕ (mul-ℕ k (succ-ℕ x)) y)
              ( pair k refl))
            ( is-difference-dist-ℕ (mul-ℕ k (succ-ℕ x)) y H))))
  f (inr H) =
    pair
      ( neg-one-unit-Fin)
      ( ( mul-neg-one-Fin (mod-succ-ℕ x (dist-ℕ (mul-ℕ k (succ-ℕ x)) y))) ∙
        ( eq-mod-succ-cong-ℕ x
           ( dist-ℕ
             ( nat-Fin (mod-succ-ℕ x (dist-ℕ (mul-ℕ k (succ-ℕ x)) y)))
             ( succ-ℕ x))
           ( y)
           ( {!!})))
    -- cong-nat-mod-succ-ℕ x (dist-ℕ (mul-ℕ k (succ-ℕ x)) y)

div-is-linear-combination-dist-ℕ :
  (x y z : ℕ) → is-linear-combination-dist-ℕ (succ-ℕ x) y z →
  div-Fin (mod-succ-ℕ x y) (mod-succ-ℕ x z)
div-is-linear-combination-dist-ℕ x y z (pair k (pair l p)) =
  pair (mod-succ-ℕ x l) {!!}

is-decidable-is-linear-combination-dist-ℕ :
  (x y z : ℕ) → is-decidable (is-linear-combination-dist-ℕ x y z)
is-decidable-is-linear-combination-dist-ℕ x y z = {!!}

Bezout :
  (x y : ℕ) →
  Σ ℕ (λ k → Σ ℕ (λ l → Id (dist-ℕ (mul-ℕ k x) (mul-ℕ l y)) (gcd-ℕ x y)))
Bezout x y =
  pair
    {!!}
    ( pair
      {!!}
      {!!})
-}

{-
 l := x / gcd x y
 k := y / gcd x y
 k x + l y = (x y / gcd x y) + (x y / gcd x y) = 2 * lcm x y
-}

--------------------------------------------------------------------------------

{- Exercise 8.12 -}

--------------------------------------------------------------------------------

{- Exercise 8.13 -}

--------------------------------------------------------------------------------

{- Exercise 8.14 -}

--------------------------------------------------------------------------------

{- Exercise 8.15 -}

-- We solve this exercise in extra/cofibonacci.agda

--------------------------------------------------------------------------------

leq-Fin :
  {k : ℕ} → Fin k → Fin k → UU lzero
leq-Fin {succ-ℕ k} (inl x) (inl y) = leq-Fin x y
leq-Fin {succ-ℕ k} (inr x) (inl y) = empty
leq-Fin {succ-ℕ k} (inl x) (inr y) = unit
leq-Fin {succ-ℕ k} (inr x) (inr y) = unit

leq-neg-one-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → leq-Fin x neg-one-Fin
leq-neg-one-Fin (inl x) = star
leq-neg-one-Fin (inr x) = star

refl-leq-Fin :
  {k : ℕ} (x : Fin k) → leq-Fin x x
refl-leq-Fin {succ-ℕ k} (inl x) = refl-leq-Fin x
refl-leq-Fin {succ-ℕ k} (inr star) = star

antisymmetric-leq-Fin :
  {k : ℕ} {x y : Fin k} → leq-Fin x y → leq-Fin y x → Id x y
antisymmetric-leq-Fin {succ-ℕ k} {inl x} {inl y} H K =
  ap inl (antisymmetric-leq-Fin H K)
antisymmetric-leq-Fin {succ-ℕ k} {inr star} {inr star} H K = refl

transitive-leq-Fin :
  {k : ℕ} {x y z : Fin k} → leq-Fin x y → leq-Fin {k} y z → leq-Fin {k} x z
transitive-leq-Fin {succ-ℕ k} {inl x} {inl y} {inl z} H K =
  transitive-leq-Fin {k} H K
transitive-leq-Fin {succ-ℕ k} {inl x} {inl y} {inr star} H K = star
transitive-leq-Fin {succ-ℕ k} {inl x} {inr star} {inr star} H K = star
transitive-leq-Fin {succ-ℕ k} {inr star} {inr star} {inr star} H K = star

concatenate-eq-leq-eq-Fin :
  {k : ℕ} {x1 x2 x3 x4 : Fin k} →
  Id x1 x2 → leq-Fin x2 x3 → Id x3 x4 → leq-Fin x1 x4
concatenate-eq-leq-eq-Fin refl H refl = H

leq-succ-Fin :
  {k : ℕ} (x : Fin k) → leq-Fin (inl-Fin k x) (succ-Fin (inl-Fin k x))
leq-succ-Fin {succ-ℕ k} (inl x) = leq-succ-Fin x
leq-succ-Fin {succ-ℕ k} (inr star) = star

preserves-leq-nat-Fin :
  {k : ℕ} {x y : Fin k} → leq-Fin x y → leq-ℕ (nat-Fin x) (nat-Fin y)
preserves-leq-nat-Fin {succ-ℕ k} {inl x} {inl y} H =
  preserves-leq-nat-Fin {k} H
preserves-leq-nat-Fin {succ-ℕ k} {inl x} {inr star} H =
  leq-le-ℕ {nat-Fin x} {k} (strict-upper-bound-nat-Fin x)
preserves-leq-nat-Fin {succ-ℕ k} {inr star} {inr star} H =
  refl-leq-ℕ k

reflects-leq-nat-Fin :
  {k : ℕ} {x y : Fin k} → leq-ℕ (nat-Fin x) (nat-Fin y) → leq-Fin x y
reflects-leq-nat-Fin {succ-ℕ k} {inl x} {inl y} H =
  reflects-leq-nat-Fin {k} H
reflects-leq-nat-Fin {succ-ℕ k} {inr star} {inl y} H =
  ex-falso (contradiction-le-ℕ (nat-Fin y) k (strict-upper-bound-nat-Fin y) H)
reflects-leq-nat-Fin {succ-ℕ k} {inl x} {inr star} H = star
reflects-leq-nat-Fin {succ-ℕ k} {inr star} {inr star} H = star

is-lower-bound-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → Fin k → UU l
is-lower-bound-Fin {l} {k} P x =
  (y : Fin k) → P y → leq-Fin x y

minimal-element-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → UU l
minimal-element-Fin {l} {k} P =
  Σ (Fin k) (λ x → (P x) × is-lower-bound-Fin P x)

is-lower-bound-inl-Fin :
  {l : Level} {k : ℕ} {P : Fin (succ-ℕ k) → UU l} {x : Fin k} →
  is-lower-bound-Fin (P ∘ inl) x → is-lower-bound-Fin P (inl-Fin k x)
is-lower-bound-inl-Fin H (inl y) p = H y p
is-lower-bound-inl-Fin {l} {k} {P} {x} H (inr star) p =
  ( leq-neg-one-Fin (inl x))

minimal-element-decidable-subtype-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} →
  ((x : Fin k) → is-decidable (P x)) →
  Σ (Fin k) P → minimal-element-Fin P
pr1 (minimal-element-decidable-subtype-Fin {l} {succ-ℕ k} d (pair (inl x) p)) =
  inl
    ( pr1
      ( minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) (pair x p)))
pr1
  ( pr2
    ( minimal-element-decidable-subtype-Fin
      {l} {succ-ℕ k} d (pair (inl x) p))) =
  pr1
    ( pr2
      ( minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) (pair x p)))
pr2
  ( pr2
    ( minimal-element-decidable-subtype-Fin
      {l} {succ-ℕ k} d (pair (inl x) p))) =
  is-lower-bound-inl-Fin (pr2 (pr2 m))
  where
  m = minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) (pair x p)
minimal-element-decidable-subtype-Fin {l} {succ-ℕ k} {P} d (pair (inr star) p)
  with
  is-decidable-Σ-Fin (λ t → d (inl t))
... | inl t =
  pair
    ( inl (pr1 m))
    ( pair
      ( pr1 (pr2 m))
      ( is-lower-bound-inl-Fin (pr2 (pr2 m))))
  where
  m = minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) t
... | inr f =
  pair
    ( inr star)
    ( pair p g)
  where
  g : (y : Fin (succ-ℕ k)) → P y → leq-Fin (neg-one-Fin {k}) y
  g (inl y) q = ex-falso (f (pair y q))
  g (inr star) q = refl-leq-Fin (neg-one-Fin {k})

--------------------------------------------------------------------------------

-- Laws of the gcd

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

{-
distributive-mul-gcd-ℕ :
  (k a b : ℕ) → Id (mul-ℕ k (gcd-ℕ a b)) (gcd-ℕ (mul-ℕ k a) (mul-ℕ k b))
distributive-mul-gcd-ℕ zero-ℕ a b = inv is-zero-gcd-zero-zero-ℕ
distributive-mul-gcd-ℕ (succ-ℕ k) a b =
  antisymmetric-div-ℕ
    ( mul-ℕ (succ-ℕ k) (gcd-ℕ a b))
    ( gcd-ℕ (mul-ℕ (succ-ℕ k) a) (mul-ℕ (succ-ℕ k) b))
    ( div-gcd-is-common-divisor-ℕ
      ( mul-ℕ (succ-ℕ k) a)
      ( mul-ℕ (succ-ℕ k) b)
      ( mul-ℕ (succ-ℕ k) (gcd-ℕ a b))
      ( preserves-is-common-divisor-mul-ℕ (succ-ℕ k) a b
        ( gcd-ℕ a b)
        ( is-common-divisor-gcd-ℕ a b)))
    {! reflects-is-common-divisor-mul-ℕ ? ? ? ? ? (is-common-divisor-gcd-ℕ (mul-ℕ (succ-ℕ k) a) (mul-ℕ (succ-ℕ k) b))!}

distributive-quotient-div-gcd-ℕ :
  (a b d : ℕ) (H : is-common-divisor-ℕ a b d) →
  Id (quotient-div-ℕ d (gcd-ℕ a b) (div-gcd-is-common-divisor-ℕ a b d H))
     (gcd-ℕ (quotient-div-ℕ d a (pr1 H)) (quotient-div-ℕ d b (pr2 H)))
distributive-quotient-div-gcd-ℕ a b d H =
  antisymmetric-div-ℕ
    ( quotient-div-ℕ d (gcd-ℕ a b) (div-gcd-is-common-divisor-ℕ a b d H))
    ( gcd-ℕ (quotient-div-ℕ d a (pr1 H)) (quotient-div-ℕ d b (pr2 H)))
    {!!}
    {!!}
-}
```
