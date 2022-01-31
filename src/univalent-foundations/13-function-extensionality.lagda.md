---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-foundations.13-function-extensionality where

open import foundation public
open import elementary-number-theory public

-- Corollary 13.2.3. Dependent functions are sections of projection maps

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  equiv-Π-sec-pr1 : sec (pr1 {B = B}) ≃ ((x : A) → B x)
  equiv-Π-sec-pr1 =
    ( ( left-unit-law-Σ-is-contr
        ( is-contr-equiv
          ( Π-total-fam (λ x y → Id y x))
          ( inv-distributive-Π-Σ)
          ( is-contr-Π (λ x → is-contr-total-path' x)))
        ( pair id refl-htpy)) ∘e
      ( equiv-right-swap-Σ)) ∘e
    ( equiv-Σ
      ( λ s → pr1 s ~ id)
      ( distributive-Π-Σ)
      ( λ s → id-equiv))
      
-- Theorem 13.2.4

--------------------------------------------------------------------------------

-- Section 13.3 Universal properties

-- Theorem 13.3.1

abstract
  is-equiv-ev-pair :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
    is-equiv (ev-pair {C = C})
  pr1 (pr1 is-equiv-ev-pair) = ind-Σ
  pr2 (pr1 is-equiv-ev-pair) = refl-htpy
  pr1 (pr2 is-equiv-ev-pair) = ind-Σ
  pr2 (pr2 is-equiv-ev-pair) f = eq-htpy (ind-Σ (λ x y → refl))

equiv-ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : Σ A B) → C x) ≃ ((a : A) (b : B a) → C (pair a b))
pr1 equiv-ev-pair = ev-pair
pr2 equiv-ev-pair = is-equiv-ev-pair

-- Corollary 13.3.2

-- Theorem 13.3.3

ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → Id a x → UU l2} →
  ((x : A) (p : Id a x) → B x p) → B a refl
ev-refl a f = f a refl

abstract
  is-equiv-ev-refl :
    {l1 l2 : Level} {A : UU l1} (a : A)
    {B : (x : A) → Id a x → UU l2} → is-equiv (ev-refl a {B = B})
  is-equiv-ev-refl a =
    is-equiv-has-inverse
      ( ind-Id a _)
      ( λ b → refl)
      ( λ f → eq-htpy
        ( λ x → eq-htpy
          ( ind-Id a
            ( λ x' p' → Id (ind-Id a _ (f a refl) x' p') (f x' p'))
            ( refl) x)))

equiv-ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → Id a x → UU l2} →
  ((x : A) (p : Id a x) → B x p) ≃ (B a refl)
pr1 (equiv-ev-refl a) = ev-refl a
pr2 (equiv-ev-refl a) = is-equiv-ev-refl a

--------------------------------------------------------------------------------

-- Section 13.4 Composing with equivalences.

precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ((b : B) → C b) → ((a : A) → C (f a))
precomp-Π f C h a = h (f a)

-- Theorem 13.4.1

tr-precompose-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : Id x y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = refl-htpy

abstract
  is-equiv-precomp-Π-is-coherently-invertible :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-coherently-invertible f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-coherently-invertible f
    ( pair g (pair issec-g (pair isretr-g coh))) C = 
    is-equiv-has-inverse
      (λ s y → tr C (issec-g y) (s (g y)))
      ( λ s → eq-htpy (λ x → 
        ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
        ( ( tr-precompose-fam C f (isretr-g x) (s (g (f x)))) ∙
          ( apd s (isretr-g x)))))
      ( λ s → eq-htpy λ y → apd s (issec-g y))

abstract
  is-equiv-precomp-Π-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-equiv f is-equiv-f =
    is-equiv-precomp-Π-is-coherently-invertible f
      ( is-coherently-invertible-is-path-split f
        ( is-path-split-is-equiv f is-equiv-f))

equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
pr1 (equiv-precomp-Π e C) = precomp-Π (map-equiv e) C
pr2 (equiv-precomp-Π e C) =
  is-equiv-precomp-Π-is-equiv (map-equiv e) (is-equiv-map-equiv e) C

abstract
  ind-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f) →
    ((x : A) → C (f x)) → ((y : B) → C y)
  ind-is-equiv C f is-equiv-f =
    map-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C)
  
  comp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
    (f : A → B) (is-equiv-f : is-equiv f) (h : (x : A) → C (f x)) →
    Id (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) h
  comp-is-equiv C f is-equiv-f h =
    issec-map-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C) h
  
  htpy-comp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f)
    (h : (x : A) → C (f x)) →
    (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) ~ h
  htpy-comp-is-equiv C f is-equiv-f h = htpy-eq (comp-is-equiv C f is-equiv-f h)

precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (B → C) → (A → C)
precomp f C = precomp-Π f (λ b → C)

abstract
  is-equiv-precomp-is-equiv-precomp-Π :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((C : B → UU l3) → is-equiv (precomp-Π f C)) →
    ((C : UU l3) → is-equiv (precomp f C))
  is-equiv-precomp-is-equiv-precomp-Π f is-equiv-precomp-Π-f C =
    is-equiv-precomp-Π-f (λ y → C)

abstract
  is-equiv-precomp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : UU l3) → is-equiv (precomp f C)
  is-equiv-precomp-is-equiv f is-equiv-f =
    is-equiv-precomp-is-equiv-precomp-Π f
      ( is-equiv-precomp-Π-is-equiv f is-equiv-f)

equiv-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (C : UU l3) →
  (B → C) ≃ (A → C)
pr1 (equiv-precomp e C) = precomp (map-equiv e) C
pr2 (equiv-precomp e C) =
  is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) C

abstract
  is-equiv-is-equiv-precomp-subuniverse :
    { l1 l2 : Level}
    ( α : Level → Level) (P : (l : Level) → UU l → UU (α l))
    ( A : Σ (UU l1) (P l1)) (B : Σ (UU l2) (P l2)) (f : pr1 A → pr1 B) →
    ( (l : Level) (C : Σ (UU l) (P l)) →
      is-equiv (precomp f (pr1 C))) →
    is-equiv f
  is-equiv-is-equiv-precomp-subuniverse α P A B f is-equiv-precomp-f =
    let retr-f = center (is-contr-map-is-equiv (is-equiv-precomp-f _ A) id) in
    is-equiv-has-inverse
      ( pr1 retr-f)
      ( htpy-eq
        ( ap ( pr1)
             ( eq-is-contr'
               ( is-contr-map-is-equiv (is-equiv-precomp-f _ B) f)
                 ( pair
                   ( f ∘ (pr1 retr-f))
                   ( ap (λ (g : pr1 A → pr1 A) → f ∘ g) (pr2 retr-f)))
                 ( pair id refl))))
      ( htpy-eq (pr2 retr-f))

abstract
  is-equiv-is-equiv-precomp :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((l : Level) (C : UU l) → is-equiv (precomp f C)) → is-equiv f
  is-equiv-is-equiv-precomp {A = A} {B = B} f is-equiv-precomp-f =
    is-equiv-is-equiv-precomp-subuniverse
      ( const Level Level lzero)
      ( λ l X → unit)
      ( pair A star)
      ( pair B star)
      ( f)
      ( λ l C → is-equiv-precomp-f l (pr1 C))

is-equiv-is-equiv-precomp-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2)
  (f : type-Prop P → type-Prop Q) →
  ({l : Level} (R : UU-Prop l) → is-equiv (precomp f (type-Prop R))) →
  is-equiv f
is-equiv-is-equiv-precomp-Prop P Q f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-prop) P Q f (λ l → H {l})

is-equiv-is-equiv-precomp-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2)
  (f : type-Set A → type-Set B) →
  ({l : Level} (C : UU-Set l) → is-equiv (precomp f (type-Set C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Set A B f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-set) A B f (λ l → H {l})

is-equiv-is-equiv-precomp-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋)
  (A : UU-Truncated-Type k l1) (B : UU-Truncated-Type k l2)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  ({l : Level} (C : UU-Truncated-Type k l) → is-equiv (precomp f (pr1 C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Truncated-Type k A B f H =
    is-equiv-is-equiv-precomp-subuniverse id (λ l → is-trunc k) A B f
      ( λ l → H {l})

--------------------------------------------------------------------------------

-- Section 13.5 The strong induction principle of ℕ

-- We prove that the induction principle for ℕ implies strong induction.

-- We first prove some lemmas about inequality.

is-prop-leq-ℕ :
  (m n : ℕ) → is-prop (leq-ℕ m n)
is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n

leq-ℕ-Prop : ℕ → ℕ → UU-Prop lzero
pr1 (leq-ℕ-Prop m n) = leq-ℕ m n
pr2 (leq-ℕ-Prop m n) = is-prop-leq-ℕ m n

neg-succ-leq-ℕ :
  (n : ℕ) → ¬ (leq-ℕ (succ-ℕ n) n)
neg-succ-leq-ℕ zero-ℕ = id
neg-succ-leq-ℕ (succ-ℕ n) = neg-succ-leq-ℕ n

leq-eq-left-ℕ :
  {m m' : ℕ} → Id m m' → (n : ℕ) → leq-ℕ m n → leq-ℕ m' n
leq-eq-left-ℕ refl n = id

leq-eq-right-ℕ :
  (m : ℕ) {n n' : ℕ} → Id n n' → leq-ℕ m n → leq-ℕ m n'
leq-eq-right-ℕ m refl = id

cases-leq-succ-ℕ :
  {m n : ℕ} → leq-ℕ m (succ-ℕ n) → coprod (leq-ℕ m n) (Id m (succ-ℕ n))
cases-leq-succ-ℕ {zero-ℕ} {n} star = inl star
cases-leq-succ-ℕ {succ-ℕ m} {zero-ℕ} p =
  inr (ap succ-ℕ (antisymmetric-leq-ℕ m zero-ℕ p star))
cases-leq-succ-ℕ {succ-ℕ m} {succ-ℕ n} p =
  map-coprod id (ap succ-ℕ) (cases-leq-succ-ℕ p)

□-≤-ℕ : {l : Level} → (ℕ → UU l) → ℕ → UU l
□-≤-ℕ P n = (m : ℕ) → (m ≤-ℕ n) → P m

η-□-≤-ℕ : {l : Level} {P : ℕ → UU l} → ((n : ℕ) → P n) → (n : ℕ) → □-≤-ℕ P n
η-□-≤-ℕ f n m p = f m

ε-□-≤-ℕ :
  {l : Level} {P : ℕ → UU l} → ((n : ℕ) → □-≤-ℕ P n) → ((n : ℕ) → P n)
ε-□-≤-ℕ f n = f n n (refl-leq-ℕ n)

-- Now we begin with the proof of the theorem
 
-- We first take care of the zero case, with appropriate computation rule.

zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → P zero-ℕ → □-≤-ℕ P zero-ℕ
zero-strong-ind-ℕ P p0 zero-ℕ t = p0

eq-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) (t : leq-ℕ zero-ℕ zero-ℕ) →
  Id (zero-strong-ind-ℕ P p0 zero-ℕ t) p0
eq-zero-strong-ind-ℕ P p0 t = refl

-- Next, we take care of the successor case, with appropriate computation rule.

{- In the successor case, we need to define a map

   □-≤-ℕ P k → □-≤-ℕ P (succ-ℕ k).

   The dependent function in the codomain is defined by case analysis, where
   the cases are that either m ≤ k or m = k+1.
   -}
   
cases-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (n : ℕ) → (□-≤-ℕ P n) → P (succ-ℕ n)) (n : ℕ)
  (H : □-≤-ℕ P n) (m : ℕ) (c : coprod (leq-ℕ m n) (Id m (succ-ℕ n))) → P m
cases-succ-strong-ind-ℕ P pS n H m (inl q) = H m q
cases-succ-strong-ind-ℕ P pS n H .(succ-ℕ n) (inr refl) = pS n H

succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → ((k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))
succ-strong-ind-ℕ P pS k H m p =
  cases-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p)

-- We use a similar case analysis to obtain the computation rule.

cases-htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (c : coprod (leq-ℕ m k) (Id m (succ-ℕ k))) →
  (q : leq-ℕ m k) →
  Id ( cases-succ-strong-ind-ℕ P pS k H m c)
     ( H m q)
cases-htpy-succ-strong-ind-ℕ P pS k H m (inl p) q =
  ap (H m) (eq-is-prop (is-prop-leq-ℕ m k))
cases-htpy-succ-strong-ind-ℕ P pS k H m (inr α) q =
  ex-falso (neg-succ-leq-ℕ k (leq-eq-left-ℕ α k q))

htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (p : leq-ℕ m (succ-ℕ k)) (q : leq-ℕ m k) →
  Id ( succ-strong-ind-ℕ P pS k H m p)
     ( H m q)
htpy-succ-strong-ind-ℕ P pS k H m p q =
  cases-htpy-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p) q

cases-eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k)
  (c : coprod (leq-ℕ (succ-ℕ k) k) (Id (succ-ℕ k) (succ-ℕ k))) →
  Id ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k) c))
     ( pS k H)
cases-eq-succ-strong-ind-ℕ P pS k H (inl p) = ex-falso (neg-succ-leq-ℕ k p)
cases-eq-succ-strong-ind-ℕ P pS k H (inr α) =
  ap ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k)) ∘ inr)
     ( eq-is-prop' (is-set-ℕ (succ-ℕ k) (succ-ℕ k)) α refl)

eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (p : leq-ℕ (succ-ℕ k) (succ-ℕ k)) →
  Id ( (succ-strong-ind-ℕ P pS k H (succ-ℕ k) p))
     ( pS k H)
eq-succ-strong-ind-ℕ P pS k H p =
  cases-eq-succ-strong-ind-ℕ P pS k H (cases-leq-succ-ℕ p)

{- Now that we have the base case and inductive step covered, we can proceed
   by induction. -}

induction-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → (□-≤-ℕ P zero-ℕ) →
  ((k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) → (n : ℕ) → □-≤-ℕ P n
induction-strong-ind-ℕ P q0 qS zero-ℕ = q0
induction-strong-ind-ℕ P q0 qS (succ-ℕ n) =
  qS n (induction-strong-ind-ℕ P q0 qS n)

computation-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (q0 : □-≤-ℕ P zero-ℕ) →
  (qS : (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) →
  (n : ℕ) →
  Id ( induction-strong-ind-ℕ P q0 qS (succ-ℕ n))
     ( qS n (induction-strong-ind-ℕ P q0 qS n))
computation-succ-strong-ind-ℕ P q0 qS n = refl

{- We are finally ready to put things together and define strong-ind-ℕ. -}

strong-ind-ℕ :
  {l : Level} → (P : ℕ → UU l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) (n : ℕ) → P n
strong-ind-ℕ P p0 pS = 
  ε-□-≤-ℕ
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS))

{- The computation rule for the base case holds by definition. -}

comp-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  Id (strong-ind-ℕ P p0 pS zero-ℕ) p0
comp-zero-strong-ind-ℕ P p0 pS = refl

{- For the computation rule of the inductive step, we use our hard work. -}

cases-leq-succ-reflexive-leq-ℕ :
  {n : ℕ} → Id (cases-leq-succ-ℕ {succ-ℕ n} {n} (refl-leq-ℕ n)) (inr refl)
cases-leq-succ-reflexive-leq-ℕ {zero-ℕ} = refl
cases-leq-succ-reflexive-leq-ℕ {succ-ℕ n} =
  ap (map-coprod id (ap succ-ℕ)) cases-leq-succ-reflexive-leq-ℕ
  
cases-eq-comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( α :
    ( m : ℕ) (p : leq-ℕ m n) →
    Id ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
         ( λ k z m₁ z₁ →
           cases-succ-strong-ind-ℕ P pS k z m₁ (cases-leq-succ-ℕ z₁))
         n m p)
     ( strong-ind-ℕ P p0 pS m)) →
  ( m : ℕ) (p : leq-ℕ m (succ-ℕ n)) →
  ( q : coprod (leq-ℕ m n) (Id m (succ-ℕ n))) →
  Id ( succ-strong-ind-ℕ P pS n
       ( induction-strong-ind-ℕ P
         ( zero-strong-ind-ℕ P p0)
         ( succ-strong-ind-ℕ P pS) n) m p)
     ( strong-ind-ℕ P p0 pS m)
cases-eq-comp-succ-strong-ind-ℕ P p0 pS n α m p (inl x) =
  ( htpy-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    m p x) ∙
  ( α m x)
cases-eq-comp-succ-strong-ind-ℕ P p0 pS n α .(succ-ℕ n) p (inr refl) =
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    ( p)) ∙
  ( inv
    ( ap
      ( cases-succ-strong-ind-ℕ P pS n
        ( induction-strong-ind-ℕ P
          ( zero-strong-ind-ℕ P p0)
          ( λ k H m p₁ →
            cases-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p₁))
          n)
        ( succ-ℕ n))
       cases-leq-succ-reflexive-leq-ℕ))

eq-comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( m : ℕ) (p : leq-ℕ m n) →
  Id ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
       ( λ k z m₁ z₁ →
         cases-succ-strong-ind-ℕ P pS k z m₁ (cases-leq-succ-ℕ z₁))
       n m p)
     ( strong-ind-ℕ P p0 pS m)
eq-comp-succ-strong-ind-ℕ P p0 pS zero-ℕ zero-ℕ star = refl
eq-comp-succ-strong-ind-ℕ P p0 pS zero-ℕ (succ-ℕ m) ()
eq-comp-succ-strong-ind-ℕ P p0 pS (succ-ℕ n) m p =
  cases-eq-comp-succ-strong-ind-ℕ P p0 pS n
    ( eq-comp-succ-strong-ind-ℕ P p0 pS n) m p
    ( cases-leq-succ-ℕ p)

comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  Id (strong-ind-ℕ P p0 pS (succ-ℕ n)) (pS n (λ m p → strong-ind-ℕ P p0 pS m))
comp-succ-strong-ind-ℕ P p0 pS n = 
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS)
      ( n))
    ( refl-leq-ℕ n)) ∙
  ( ap ( pS n)
       ( eq-htpy
         ( λ m → eq-htpy
           ( λ p → eq-comp-succ-strong-ind-ℕ P p0 pS n m p))))

total-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  Σ ( (n : ℕ) → P n)
    ( λ h →
      ( Id (h zero-ℕ) p0) ×
      ( (n : ℕ) → Id (h (succ-ℕ n)) (pS n (λ m p → h m))))
pr1 (total-strong-ind-ℕ P p0 pS) = strong-ind-ℕ P p0 pS
pr1 (pr2 (total-strong-ind-ℕ P p0 pS)) = comp-zero-strong-ind-ℕ P p0 pS
pr2 (pr2 (total-strong-ind-ℕ P p0 pS)) = comp-succ-strong-ind-ℕ P p0 pS

```
