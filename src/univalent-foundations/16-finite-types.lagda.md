---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-foundations.16-finite-types where

open import univalent-foundations.15-image public

--------------------------------------------------------------------------------

-- Section 16 Finite types

--------------------------------------------------------------------------------

-- Section 16.1 Counting in type theory

-- Definition 16.1.1

count : {l : Level} → UU l → UU l
count X = Σ ℕ (λ k → Fin k ≃ X)

module _
  {l : Level} {X : UU l} (e : count X)
  where
  
  number-of-elements-count : ℕ
  number-of-elements-count = pr1 e
  
  equiv-count : Fin number-of-elements-count ≃ X
  equiv-count = pr2 e
  
  map-equiv-count : Fin number-of-elements-count → X
  map-equiv-count = map-equiv equiv-count
  
  map-inv-equiv-count : X → Fin number-of-elements-count
  map-inv-equiv-count = map-inv-equiv equiv-count
  
  inv-equiv-count : X ≃ Fin number-of-elements-count
  inv-equiv-count = inv-equiv equiv-count
  
  is-set-count : is-set X
  is-set-count =
    is-set-equiv'
      ( Fin number-of-elements-count)
      ( equiv-count)
      ( is-set-Fin number-of-elements-count)

-- Example 16.1.2

-- Fin k has a count

count-Fin : (k : ℕ) → count (Fin k)
pr1 (count-Fin k) = k
pr2 (count-Fin k) = id-equiv

-- Types equipped with countings are closed under equivalences

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where
  
  abstract
    equiv-count-equiv :
      (e : X ≃ Y) (f : count X) → Fin (number-of-elements-count f) ≃ Y
    equiv-count-equiv e f = e ∘e (equiv-count f)

  count-equiv : X ≃ Y → count X → count Y
  pr1 (count-equiv e f) = number-of-elements-count f
  pr2 (count-equiv e f) = equiv-count-equiv e f

  abstract
    equiv-count-equiv' :
      (e : X ≃ Y) (f : count Y) → Fin (number-of-elements-count f) ≃ X
    equiv-count-equiv' e f = inv-equiv e ∘e (equiv-count f)
  
  count-equiv' : X ≃ Y → count Y → count X
  pr1 (count-equiv' e f) = number-of-elements-count f
  pr2 (count-equiv' e f) = equiv-count-equiv' e f
  
  count-is-equiv : {f : X → Y} → is-equiv f → count X → count Y
  count-is-equiv H = count-equiv (pair _ H)
  
  count-is-equiv' :
    {f : X → Y} → is-equiv f → count Y → count X
  count-is-equiv' H = count-equiv' (pair _ H)

-- Example 16.1.3

-- A type as 0 elements if and only if it is empty

abstract
  is-empty-is-zero-number-of-elements-count :
    {l : Level} {X : UU l} (e : count X) →
    is-zero-ℕ (number-of-elements-count e) → is-empty X
  is-empty-is-zero-number-of-elements-count (pair .zero-ℕ e) refl x =
    map-inv-equiv e x

abstract
  is-zero-number-of-elements-count-is-empty :
    {l : Level} {X : UU l} (e : count X) →
    is-empty X → is-zero-ℕ (number-of-elements-count e)
  is-zero-number-of-elements-count-is-empty (pair zero-ℕ e) H = refl
  is-zero-number-of-elements-count-is-empty (pair (succ-ℕ k) e) H =
    ex-falso (H (map-equiv e zero-Fin))

count-is-empty :
  {l : Level} {X : UU l} → is-empty X → count X
pr1 (count-is-empty H) = zero-ℕ
pr2 (count-is-empty H) = inv-equiv (pair H (is-equiv-is-empty' H))

count-empty : count empty
count-empty = count-Fin zero-ℕ

-- Example 16.1.4

-- A type has 1 element if and only if it is contractible

count-is-contr :
  {l : Level} {X : UU l} → is-contr X → count X
pr1 (count-is-contr H) = one-ℕ
pr2 (count-is-contr H) = equiv-is-contr is-contr-Fin-one-ℕ H

abstract
  is-contr-is-one-number-of-elements-count :
    {l : Level} {X : UU l} (e : count X) →
    is-one-ℕ (number-of-elements-count e) → is-contr X
  is-contr-is-one-number-of-elements-count (pair .(succ-ℕ zero-ℕ) e) refl =
    is-contr-equiv' (Fin one-ℕ) e is-contr-Fin-one-ℕ

abstract
  is-one-number-of-elements-count-is-contr :
    {l : Level} {X : UU l} (e : count X) →
    is-contr X → is-one-ℕ (number-of-elements-count e)
  is-one-number-of-elements-count-is-contr (pair zero-ℕ e) H =
    ex-falso (map-inv-equiv e (center H))
  is-one-number-of-elements-count-is-contr (pair (succ-ℕ zero-ℕ) e) H =
    refl
  is-one-number-of-elements-count-is-contr (pair (succ-ℕ (succ-ℕ k)) e) H =
    ex-falso
      ( Eq-Fin-eq
        ( is-injective-map-equiv e
          ( eq-is-contr' H (map-equiv e zero-Fin) (map-equiv e neg-one-Fin))))

count-unit : count unit
count-unit = count-is-contr is-contr-unit

-- Example 16.1.5

-- Propositions have countings if and only if they are decidable

is-decidable-count :
  {l : Level} {X : UU l} → count X → is-decidable X
is-decidable-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-decidable-count (pair (succ-ℕ k) e) =
  inl (map-equiv e zero-Fin)

count-is-decidable-is-prop :
  {l : Level} {A : UU l} → is-prop A → is-decidable A → count A
count-is-decidable-is-prop H (inl x) =
  count-is-contr (is-proof-irrelevant-is-prop H x)
count-is-decidable-is-prop H (inr f) = count-is-empty f

count-decidable-Prop :
  {l1 : Level} (P : UU-Prop l1) →
  is-decidable (type-Prop P) → count (type-Prop P)
count-decidable-Prop P (inl p) =
  count-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) p)
count-decidable-Prop P (inr f) = count-is-empty f

-- Example 16.1.6

-- Types with a count have decidable equality

has-decidable-equality-count :
  {l : Level} {X : UU l} → count X → has-decidable-equality X
has-decidable-equality-count (pair k e) =
  has-decidable-equality-equiv' e has-decidable-equality-Fin

{- We can count the elements of an identity type of a type that has decidable
   equality. -}

cases-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (Id x y)) → count (Id x y)
cases-count-eq d {x} {y} (inl p) =
  count-is-contr
    ( is-proof-irrelevant-is-prop (is-set-has-decidable-equality d x y) p)
cases-count-eq d (inr f) =
  count-is-empty f

count-eq :
  {l : Level} {X : UU l} → has-decidable-equality X → (x y : X) → count (Id x y)
count-eq d x y = cases-count-eq d (d x y)

cases-number-of-elements-count-eq' :
  {l : Level} {X : UU l} {x y : X} →
  is-decidable (Id x y) → ℕ
cases-number-of-elements-count-eq' (inl p) = one-ℕ
cases-number-of-elements-count-eq' (inr f) = zero-ℕ

number-of-elements-count-eq' :
  {l : Level} {X : UU l} (d : has-decidable-equality X) (x y : X) → ℕ
number-of-elements-count-eq' d x y =
  cases-number-of-elements-count-eq' (d x y)

cases-number-of-elements-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (Id x y)) →
  Id ( number-of-elements-count (cases-count-eq d e))
     ( cases-number-of-elements-count-eq' e)
cases-number-of-elements-count-eq d (inl p) = refl
cases-number-of-elements-count-eq d (inr f) = refl

abstract
  number-of-elements-count-eq :
    {l : Level} {X : UU l} (d : has-decidable-equality X) (x y : X) →
    Id ( number-of-elements-count (count-eq d x y))
      ( number-of-elements-count-eq' d x y)
  number-of-elements-count-eq d x y =
    cases-number-of-elements-count-eq d (d x y)

-- Theorem 16.1.7

-- Theorem 16.1.7 (i) Forward direction

-- Types equipped with a count are closed under coproducts

count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (coprod X Y)
pr1 (count-coprod (pair k e) (pair l f)) = add-ℕ k l
pr2 (count-coprod (pair k e) (pair l f)) =
  (equiv-coprod e f) ∘e (inv-equiv (coprod-Fin k l))

abstract
  number-of-elements-count-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
    Id ( number-of-elements-count (count-coprod e f))
      ( add-ℕ (number-of-elements-count e) (number-of-elements-count f))
  number-of-elements-count-coprod (pair k e) (pair l f) = refl

-- Theorem 16.1.7 (ii) (a) Forward direction

count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) (e : Fin k ≃ A) → ((x : A) → count (B x)) → count (Σ A B)
count-Σ' zero-ℕ e f =
  count-is-empty
    ( λ x →
      is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl (pr1 x))
count-Σ' {l1} {l2} {A} {B} (succ-ℕ k) e f =
  count-equiv
    ( ( equiv-Σ-equiv-base B e) ∘e
      ( ( inv-equiv
          ( right-distributive-Σ-coprod (Fin k) unit (B ∘ map-equiv e))) ∘e
        ( equiv-coprod
          ( id-equiv)
          ( inv-equiv
            ( left-unit-law-Σ (B ∘ (map-equiv e ∘ inr)))))))
    ( count-coprod
      ( count-Σ' k id-equiv (λ x → f (map-equiv e (inl x))))
      ( f (map-equiv e (inr star))))

abstract
  equiv-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    (k : ℕ) (e : Fin k ≃ A) (f : (x : A) → count (B x)) →
    Fin (number-of-elements-count (count-Σ' k e f)) ≃ Σ A B
  equiv-count-Σ' k e f = pr2 (count-Σ' k e f)

count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count (Σ A B)
pr1 (count-Σ (pair k e) f) = number-of-elements-count (count-Σ' k e f)
pr2 (count-Σ (pair k e) f) = equiv-count-Σ' k e f

{- In order to compute the number of elements of a Σ-type, We introduce finite 
   sums and sums indexed by counted types. -}

sum-Fin-ℕ : {k : ℕ} → (Fin k → ℕ) → ℕ
sum-Fin-ℕ {zero-ℕ} f = zero-ℕ
sum-Fin-ℕ {succ-ℕ k} f = add-ℕ (sum-Fin-ℕ (λ x → f (inl x))) (f (inr star))

abstract
  htpy-sum-Fin-ℕ :
    {k : ℕ} {f g : Fin k → ℕ} (H : f ~ g) → Id (sum-Fin-ℕ f) (sum-Fin-ℕ g)
  htpy-sum-Fin-ℕ {zero-ℕ} H = refl
  htpy-sum-Fin-ℕ {succ-ℕ k} H =
    ap-add-ℕ
      ( htpy-sum-Fin-ℕ (λ x → H (inl x)))
      ( H (inr star))

abstract
  constant-sum-Fin-ℕ :
    (m n : ℕ) → Id (sum-Fin-ℕ (const (Fin m) ℕ n)) (mul-ℕ m n)
  constant-sum-Fin-ℕ zero-ℕ n = refl
  constant-sum-Fin-ℕ (succ-ℕ m) n = ap (add-ℕ' n) (constant-sum-Fin-ℕ m n)

sum-count-ℕ : {l : Level} {A : UU l} (e : count A) → (f : A → ℕ) → ℕ
sum-count-ℕ (pair k e) f = sum-Fin-ℕ (f ∘ (map-equiv e))

abstract
  ap-sum-count-ℕ :
    {l : Level} {A : UU l} (e : count A) {f g : A → ℕ} (H : f ~ g) →
    Id (sum-count-ℕ e f) (sum-count-ℕ e g)
  ap-sum-count-ℕ (pair k e) H = htpy-sum-Fin-ℕ (H ·r (map-equiv e))

abstract
  constant-sum-count-ℕ :
    {l : Level} {A : UU l} (e : count A) (n : ℕ) →
    Id (sum-count-ℕ e (const A ℕ n)) (mul-ℕ (number-of-elements-count e) n)
  constant-sum-count-ℕ (pair m e) n = constant-sum-Fin-ℕ m n

-- We compute the number of elements of a Σ-type

abstract
  number-of-elements-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (k : ℕ) (e : Fin k ≃ A) →
    (f : (x : A) → count (B x)) →
    Id ( number-of-elements-count (count-Σ' k e f))
      ( sum-Fin-ℕ (λ x → number-of-elements-count (f (map-equiv e x)))) 
  number-of-elements-count-Σ' zero-ℕ e f = refl
  number-of-elements-count-Σ' (succ-ℕ k) e f =
    ( number-of-elements-count-coprod
      ( count-Σ' k id-equiv (λ x → f (map-equiv e (inl x))))
      ( f (map-equiv e (inr star)))) ∙
    ( ap
      ( add-ℕ' (number-of-elements-count (f (map-equiv e (inr star)))))
      ( number-of-elements-count-Σ' k id-equiv (λ x → f (map-equiv e (inl x)))))

abstract
  number-of-elements-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
    (f : (x : A) → count (B x)) →
    Id ( number-of-elements-count (count-Σ e f))
      ( sum-count-ℕ e (λ x → number-of-elements-count (f x)))
  number-of-elements-count-Σ (pair k e) f = number-of-elements-count-Σ' k e f

-- Theorem 16.1.7 (ii) (a) Converse direction

-- We show that if A and Σ A B can be counted, then each B x can be counted

count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → count (Σ A B) → (x : A) → count (B x)
count-fiber-count-Σ {B = B} e f x =
  count-equiv
    ( equiv-fib-pr1 B x)
    ( count-Σ f
      ( λ z → count-eq (has-decidable-equality-count e) (pr1 z) x))

{- As a corollary we obtain that if A and B can be counted, then the fibers of
   a map f : A → B can be counted. -}

count-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  count A → count B → (y : B) → count (fib f y)
count-fib f count-A count-B =
  count-fiber-count-Σ count-B (count-equiv' (equiv-total-fib f) count-A)

-- Theorem 16.1.7 (ii) (b)

{- If Σ A B and each B x can be counted, and if B has a section, then A can be
   counted. -}

equiv-total-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  Σ (Σ A B) (fib (map-section b)) ≃ A
equiv-total-fib-map-section b = equiv-total-fib (map-section b)

count-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) →
  (t : Σ A B) → count (fib (map-section b) t)
count-fib-map-section {l1} {l2} {A} {B} b e f (pair y z) =
  count-equiv'
    ( ( ( left-unit-law-Σ-is-contr
            ( is-contr-total-path' y)
            ( pair y refl)) ∘e
        ( inv-assoc-Σ A
          ( λ x → Id x y)
          ( λ t → Id (tr B (pr2 t) (b (pr1 t))) z))) ∘e
      ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
    ( count-eq (has-decidable-equality-count (f y)) (b y) z)

count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) → count A
count-base-count-Σ b e f =
  count-equiv
    ( equiv-total-fib-map-section b)
    ( count-Σ e (count-fib-map-section b e f))

{- More generally, if Σ A B and each B x can be counted, then A can be counted
   if and only if the type Σ A (¬ ∘ B) can be counted. However, to avoid having
   to invoke function extensionality, we show that if Σ A B and each B x can be
   counted, then A can be counted if and only if

   count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))),

   where f : (x : A) → count (B x). 

   Thus, we have a precise characterization of when A can be counted, if it is 
   given that Σ A B and each B x can be counted. -}

section-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) →
  (x : A) → coprod (B x) (is-zero-ℕ (number-of-elements-count (f x)))
section-count-base-count-Σ' e f g x with
  is-decidable-is-zero-ℕ (number-of-elements-count (f x))
... | inl p = inr p
... | inr H with is-successor-is-nonzero-ℕ H
... | (pair k p) = inl (map-equiv-count (f x) (tr Fin (inv p) zero-Fin))

count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) → count A
count-base-count-Σ' {l1} {l2} {A} {B} e f g =
  count-base-count-Σ
    ( section-count-base-count-Σ' e f g)
    ( count-equiv'
      ( left-distributive-Σ-coprod A B
        ( λ x → is-zero-ℕ (number-of-elements-count (f x))))
      ( count-coprod e g))
    ( λ x →
      count-coprod
        ( f x)
        ( count-eq has-decidable-equality-ℕ
          ( number-of-elements-count (f x))
          ( zero-ℕ)))

-- Theorem 16.1.7 (ii) Consequences

-- A decidable subtype of a type that can be counted can be counted

count-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} (P : X → UU-Prop l2) →
  ((x : X) → is-decidable (type-Prop (P x))) →
  count X → count (Σ X (λ x → type-Prop (P x)))
count-decidable-subtype P d e =
  count-Σ e (λ x → count-decidable-Prop (P x) (d x))

{- If A can be counted and Σ A P can be counted for a subtype of A, then P is
   decidable -}

is-decidable-count-Σ :
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  count X → count (Σ X P) → (x : X) → is-decidable (P x)
is-decidable-count-Σ e f x =
  is-decidable-count (count-fiber-count-Σ e f x)

is-decidable-count-subtype :
  {l1 l2 : Level} {X : UU l1} (P : X → UU-Prop l2) → count X →
  count (Σ X (λ x → type-Prop (P x))) → (x : X) → is-decidable (type-Prop (P x))
is-decidable-count-subtype P = is-decidable-count-Σ

-- Theorem 16.1.7 (i) Converse direction

-- A coproduct X + Y has a count if and only if both X and Y have a count.

is-left : {l1 l2 : Level} {X : UU l1} {Y : UU l2} → coprod X Y → UU lzero
is-left (inl x) = unit
is-left (inr x) = empty

equiv-left-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Σ (coprod X Y) is-left) ≃ X
equiv-left-summand {l1} {l2} {X} {Y} =
  ( ( right-unit-law-coprod X) ∘e
    ( equiv-coprod right-unit-law-prod (right-absorption-prod Y))) ∘e
  ( right-distributive-Σ-coprod X Y is-left)

count-is-left :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (t : coprod X Y) → count (is-left t)
count-is-left (inl x) = count-unit
count-is-left (inr x) = count-empty

count-left-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count X
count-left-coprod e = count-equiv equiv-left-summand (count-Σ e count-is-left)

is-right : {l1 l2 : Level} {X : UU l1} {Y : UU l2} → coprod X Y → UU lzero
is-right (inl x) = empty
is-right (inr x) = unit

equiv-right-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Σ (coprod X Y) is-right) ≃ Y
equiv-right-summand {l1} {l2} {X} {Y} =
  ( ( left-unit-law-coprod Y) ∘e
    ( equiv-coprod (right-absorption-prod X) right-unit-law-prod)) ∘e
    ( right-distributive-Σ-coprod X Y is-right)

count-is-right :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (t : coprod X Y) → count (is-right t)
count-is-right (inl x) = count-empty
count-is-right (inr x) = count-unit

count-right-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count Y
count-right-coprod e =
  count-equiv equiv-right-summand (count-Σ e count-is-right)

-- Corollary 16.1.8

count-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count X → count Y → count (X × Y)
pr1 (count-prod (pair k e) (pair l f)) = mul-ℕ k l
pr2 (count-prod (pair k e) (pair l f)) =
  (equiv-prod e f) ∘e (inv-equiv (prod-Fin k l))

abstract
  number-of-elements-count-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
    (count-B : count B) →
    Id ( number-of-elements-count
         ( count-prod count-A count-B))
       ( mul-ℕ
         ( number-of-elements-count count-A)
         ( number-of-elements-count count-B))
  number-of-elements-count-prod (pair k e) (pair l f) = refl

equiv-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (y : Y) →
  (Σ (X × Y) (λ t → Id (pr2 t) y)) ≃ X
equiv-left-factor {l1} {l2} {X} {Y} y =
  ( ( right-unit-law-prod) ∘e
    ( equiv-tot
      ( λ x → equiv-is-contr (is-contr-total-path' y) is-contr-unit))) ∘e
  ( assoc-Σ X (λ x → Y) (λ t → Id (pr2 t) y))

count-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → Y → count X
count-left-factor e y =
  count-equiv
    ( equiv-left-factor y)
    ( count-Σ e
      ( λ z →
        count-eq
          ( has-decidable-equality-right-factor
            ( has-decidable-equality-count e)
            ( pr1 z))
          ( pr2 z)
          ( y)))

count-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → X → count Y
count-right-factor e x =
  count-left-factor (count-equiv commutative-prod e) x

--------------------------------------------------------------------------------

-- Section 16.2 Double counting

-- Theorem 16.2.1

-- The Maybe modality

Maybe : {l : Level} → UU l → UU l
Maybe X = coprod X unit

unit-Maybe : {l : Level} {X : UU l} → X → Maybe X
unit-Maybe = inl

abstract
  is-emb-unit-Maybe : {l : Level} {X : UU l} → is-emb (unit-Maybe {X = X})
  is-emb-unit-Maybe {l} {X} = is-emb-inl X unit

abstract
  is-injective-unit-Maybe :
    {l : Level} {X : UU l} → is-injective (unit-Maybe {X = X})
  is-injective-unit-Maybe = is-injective-inl

-- The exception
exception-Maybe : {l : Level} {X : UU l} → Maybe X
exception-Maybe {l} {X} = inr star

-- The is-exception predicate
is-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-exception-Maybe {l} {X} x = Id x exception-Maybe

-- The universal property of Maybe

module _
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2}
  where

  ev-Maybe :
    ((x : Maybe A) → B x) → ((x : A) → B (unit-Maybe x)) × B exception-Maybe
  pr1 (ev-Maybe h) x = h (unit-Maybe x)
  pr2 (ev-Maybe h) = h exception-Maybe
  
  ind-Maybe :
    ((x : A) → B (unit-Maybe x)) × (B exception-Maybe) → (x : Maybe A) → B x
  ind-Maybe (pair h b) (inl x) = h x
  ind-Maybe (pair h b) (inr star) = b

  abstract
    issec-ind-Maybe : (ev-Maybe ∘ ind-Maybe) ~ id
    issec-ind-Maybe (pair h b) = refl

    isretr-ind-Maybe' :
      (h : (x : Maybe A) → B x) → (ind-Maybe (ev-Maybe h)) ~ h
    isretr-ind-Maybe' h (inl x) = refl
    isretr-ind-Maybe' h (inr star) = refl

    isretr-ind-Maybe : (ind-Maybe ∘ ev-Maybe) ~ id
    isretr-ind-Maybe h = eq-htpy (isretr-ind-Maybe' h)

    dependent-universal-property-Maybe :
      is-equiv ev-Maybe
    dependent-universal-property-Maybe =
      is-equiv-has-inverse
        ind-Maybe
        issec-ind-Maybe
        isretr-ind-Maybe

equiv-dependent-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} (B : Maybe A → UU l2) →
  ((x : Maybe A) → B x) ≃ (((x : A) → B (unit-Maybe x)) × B exception-Maybe)
pr1 (equiv-dependent-universal-property-Maybe B) = ev-Maybe
pr2 (equiv-dependent-universal-property-Maybe B) =
  dependent-universal-property-Maybe

equiv-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (Maybe A → B) ≃ ((A → B) × B)
equiv-universal-property-Maybe {l1} {l2} {A} {B} =
  equiv-dependent-universal-property-Maybe (λ x → B)

-- The is-exception predicate is decidable
is-decidable-is-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-exception-Maybe x)
is-decidable-is-exception-Maybe {l} {X} (inl x) =
  inr
    (λ p → ex-falso (map-inv-raise (Eq-eq-coprod X unit (inl x) (inr star) p)))
is-decidable-is-exception-Maybe (inr star) = inl refl

-- The is-not-exception predicate
is-not-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-not-exception-Maybe x = ¬ (is-exception-Maybe x)

abstract
  is-not-exception-unit-Maybe :
    {l : Level} {X : UU l} (x : X) → is-not-exception-Maybe (unit-Maybe x)
  is-not-exception-unit-Maybe {l} {X} x = neq-inl-inr x star

-- The is-not-exception predicate is decidable
is-decidable-is-not-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-not-exception-Maybe x)
is-decidable-is-not-exception-Maybe x =
  is-decidable-neg (is-decidable-is-exception-Maybe x)

-- The is-value predicate
is-value-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-value-Maybe {l} {X} x = Σ X (λ y → Id (inl y) x)

value-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x → X
value-is-value-Maybe x = pr1

eq-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) (H : is-value-Maybe x) →
  Id (inl (value-is-value-Maybe x H)) x
eq-is-value-Maybe x H = pr2 H

-- The decision procedure whether something is a value or an exception
decide-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) →
  coprod (is-value-Maybe x) (is-exception-Maybe x)
decide-Maybe (inl x) = inl (pair x refl)
decide-Maybe (inr star) = inr refl

-- If a point is not an exception, then it is a value
is-value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-not-exception-Maybe x → is-value-Maybe x
is-value-is-not-exception-Maybe x H =
  map-right-unit-law-coprod-is-empty (is-value-Maybe x) (is-exception-Maybe x) H (decide-Maybe x)

value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) → is-not-exception-Maybe x → X
value-is-not-exception-Maybe x H =
  value-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

eq-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) (H : is-not-exception-Maybe x) →
  Id (inl (value-is-not-exception-Maybe x H)) x
eq-is-not-exception-Maybe x H =
  eq-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

-- If a point is a value, then it is not an exception
abstract
  is-not-exception-is-value-Maybe :
    {l1 : Level} {X : UU l1} (x : Maybe X) →
    is-value-Maybe x → is-not-exception-Maybe x
  is-not-exception-is-value-Maybe {l1} {X} .(inl x) (pair x refl) =
    is-not-exception-unit-Maybe x

-- Proposition 16.2.1 Step (i) of the proof

-- If f is an injective map and f (inl x) is an exception, then f exception is
-- not an exception.

abstract
  is-not-exception-injective-map-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
    is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
    is-not-exception-Maybe (f exception-Maybe)
  is-not-exception-injective-map-exception-Maybe is-inj-f x p q =
    is-not-exception-unit-Maybe x (is-inj-f (p ∙ inv q))

abstract
  is-not-exception-map-equiv-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
    is-exception-Maybe (map-equiv e (inl x)) →
    is-not-exception-Maybe (map-equiv e exception-Maybe)
  is-not-exception-map-equiv-exception-Maybe e =
    is-not-exception-injective-map-exception-Maybe (is-injective-map-equiv e)

-- If f is injective and f (inl x) is an exception, then f exception is a value
is-value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-value-Maybe (f exception-Maybe)
is-value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  is-value-is-not-exception-Maybe
    ( f exception-Maybe)
    ( is-not-exception-injective-map-exception-Maybe is-inj-f x H)

value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) → Y
value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  value-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

comp-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (H : is-exception-Maybe (f (inl x))) →
  Id ( inl (value-injective-map-exception-Maybe is-inj-f x H))
     ( f exception-Maybe)
comp-injective-map-exception-Maybe {f = f} is-inj-f x H =
  eq-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

abstract
  is-not-exception-emb-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ↪ Maybe Y)
    (x : X) → is-exception-Maybe (map-emb e (inl x)) →
    is-not-exception-Maybe (map-emb e exception-Maybe)
  is-not-exception-emb-exception-Maybe e =
    is-not-exception-injective-map-exception-Maybe (is-injective-emb e)

-- If e (inl x) is an exception, then e exception is a value
is-value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-value-Maybe (map-equiv e exception-Maybe)
is-value-map-equiv-exception-Maybe e x H =
  is-value-is-not-exception-Maybe
    ( map-equiv e exception-Maybe)
    ( is-not-exception-map-equiv-exception-Maybe e x H)

value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) → Y
value-map-equiv-exception-Maybe e x H =
  value-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

comp-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (H : is-exception-Maybe (map-equiv e (inl x))) →
  Id ( inl (value-map-equiv-exception-Maybe e x H))
     ( map-equiv e exception-Maybe)
comp-map-equiv-exception-Maybe e x H =
  eq-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

-- Proposition 16.2.1 Step (ii) of the proof

restrict-injective-map-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) → Y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inl y) p = y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inr star) p =
  value-injective-map-exception-Maybe is-inj-f x p

restrict-injective-map-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → X → Y
restrict-injective-map-Maybe {f = f} is-inj-f x =
  restrict-injective-map-Maybe' is-inj-f x (f (inl x)) refl

comp-restrict-injective-map-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) →
  is-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe' is-inj-f x u p)) (f exception-Maybe)
comp-restrict-injective-map-is-exception-Maybe' {f = f} is-inj-f x (inl y) p q =
  ex-falso (is-not-exception-unit-Maybe y (inv p ∙ q))
comp-restrict-injective-map-is-exception-Maybe' {f = f} is-inj-f x (inr star) p q =
  comp-injective-map-exception-Maybe is-inj-f x p

comp-restrict-injective-map-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe is-inj-f x)) (f exception-Maybe)
comp-restrict-injective-map-is-exception-Maybe {f = f} is-inj-f x =
  comp-restrict-injective-map-is-exception-Maybe' is-inj-f x (f (inl x)) refl

comp-restrict-injective-map-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) →
  is-not-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe' is-inj-f x u p)) (f (inl x))
comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (inl y) p H =
  inv p
comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (inr star) p H =
  ex-falso (H p)

comp-restrict-injective-map-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-not-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe is-inj-f x)) (f (inl x))
comp-restrict-injective-map-is-not-exception-Maybe {f = f} is-inj-f x =
  comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (f (inl x))
    refl

-- An equivalence e : Maybe X ≃ Maybe Y induces a map X → Y. We don't use
-- with-abstraction to keep full control over the definitional equalities, so
-- we give the definition in two steps. After the definition is complete, we
-- also prove two computation rules. Since we will prove computation rules, we
-- make the definition abstract.

map-equiv-equiv-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y)
  (x : X) (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) → Y
map-equiv-equiv-Maybe' e =
  restrict-injective-map-Maybe' (is-injective-map-equiv e)

map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → X → Y
map-equiv-equiv-Maybe e =
  restrict-injective-map-Maybe (is-injective-map-equiv e)

comp-map-equiv-equiv-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe' e =
  comp-restrict-injective-map-is-exception-Maybe' (is-injective-map-equiv e)

comp-map-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe e x)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe e x =
  comp-map-equiv-equiv-is-exception-Maybe' e x (map-equiv e (inl x)) refl

comp-map-equiv-equiv-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e (inl x))
comp-map-equiv-equiv-is-not-exception-Maybe' e x (inl y) p H =
  inv p
comp-map-equiv-equiv-is-not-exception-Maybe' e x (inr star) p H =
  ex-falso (H p)

comp-map-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe e x)) (map-equiv e (inl x))
comp-map-equiv-equiv-is-not-exception-Maybe e x =
  comp-map-equiv-equiv-is-not-exception-Maybe' e x (map-equiv e (inl x)) refl

-- Proposition 16.2.1 Step (iii) of the proof

-- An equivalence e : Maybe X ≃ Maybe Y induces a map Y → X

map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → Y → X
map-inv-equiv-equiv-Maybe e =
  map-equiv-equiv-Maybe (inv-equiv e)

comp-map-inv-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  is-exception-Maybe (map-inv-equiv e (inl y)) →
  Id (inl (map-inv-equiv-equiv-Maybe e y)) (map-inv-equiv e exception-Maybe)
comp-map-inv-equiv-equiv-is-exception-Maybe e =
  comp-map-equiv-equiv-is-exception-Maybe (inv-equiv e)

comp-map-inv-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  ( f : is-not-exception-Maybe (map-inv-equiv e (inl y))) →
  Id (inl (map-inv-equiv-equiv-Maybe e y)) (map-inv-equiv e (inl y))
comp-map-inv-equiv-equiv-is-not-exception-Maybe e =
  comp-map-equiv-equiv-is-not-exception-Maybe (inv-equiv e)

-- Proposition 16.2.1 Step (iv) of the proof
    
-- map-inv-equiv-equiv-Maybe e is a section of map-equiv-equiv-Maybe e.

abstract
  issec-map-inv-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    (map-equiv-equiv-Maybe e ∘ map-inv-equiv-equiv-Maybe e) ~ id
  issec-map-inv-equiv-equiv-Maybe e y with
    is-decidable-is-exception-Maybe (map-inv-equiv e (inl y))
  ... | inl p =
    is-injective-unit-Maybe
      ( ( comp-map-equiv-equiv-is-exception-Maybe e
          ( map-inv-equiv-equiv-Maybe e y)
          ( ( ap
              ( map-equiv e)
              ( comp-map-inv-equiv-equiv-is-exception-Maybe e y p)) ∙
            ( issec-map-inv-equiv e exception-Maybe))) ∙
        ( ( ap (map-equiv e) (inv p)) ∙
          ( issec-map-inv-equiv e (inl y))))
  ... | inr f =
    is-injective-unit-Maybe
      ( ( comp-map-equiv-equiv-is-not-exception-Maybe e
          ( map-inv-equiv-equiv-Maybe e y)
          ( is-not-exception-is-value-Maybe
            ( map-equiv e (inl (map-inv-equiv-equiv-Maybe e y)))
            ( pair y
              ( inv
                ( ( ap
                    ( map-equiv e)
                    ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
                  ( issec-map-inv-equiv e (inl y))))))) ∙
        ( ( ap
            ( map-equiv e)
            ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
          ( issec-map-inv-equiv e (inl y))))

-- The map map-inv-equiv-equiv e is a retraction of the map map-equiv-equiv

abstract
  isretr-map-inv-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    (map-inv-equiv-equiv-Maybe e ∘ map-equiv-equiv-Maybe e) ~ id
  isretr-map-inv-equiv-equiv-Maybe e x with
    is-decidable-is-exception-Maybe (map-equiv e (inl x))
  ... | inl p =
    is-injective-unit-Maybe
      ( ( comp-map-inv-equiv-equiv-is-exception-Maybe e
          ( map-equiv-equiv-Maybe e x)
          ( ( ap ( map-inv-equiv e)
                 ( comp-map-equiv-equiv-is-exception-Maybe e x p)) ∙
            ( isretr-map-inv-equiv e exception-Maybe))) ∙
        ( ( ap (map-inv-equiv e) (inv p)) ∙
          ( isretr-map-inv-equiv e (inl x))))
  ... | inr f =
    is-injective-unit-Maybe
      ( ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e
          ( map-equiv-equiv-Maybe e x)
          ( is-not-exception-is-value-Maybe
            ( map-inv-equiv e (inl (map-equiv-equiv-Maybe e x)))
            ( pair x
              ( inv
                ( ( ap (map-inv-equiv e)
                       ( comp-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
                  ( isretr-map-inv-equiv e (inl x))))))) ∙
        ( ( ap ( map-inv-equiv e)
               ( comp-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
          ( isretr-map-inv-equiv e (inl x))))

-- Proposition 16.2.1 Conclusion of the proof

-- The function map-equiv-equiv-Maybe is an equivalence

abstract
  is-equiv-map-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    is-equiv (map-equiv-equiv-Maybe e)
  is-equiv-map-equiv-equiv-Maybe e =
    is-equiv-has-inverse
      ( map-inv-equiv-equiv-Maybe e)
      ( issec-map-inv-equiv-equiv-Maybe e)
      ( isretr-map-inv-equiv-equiv-Maybe e)

equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Maybe X ≃ Maybe Y) → (X ≃ Y)
pr1 (equiv-equiv-Maybe e) = map-equiv-equiv-Maybe e
pr2 (equiv-equiv-Maybe e) = is-equiv-map-equiv-equiv-Maybe e

-- Theorem 16.2.2

abstract
  is-injective-Fin : {k l : ℕ} → (Fin k ≃ Fin l) → Id k l
  is-injective-Fin {zero-ℕ} {zero-ℕ} e = refl
  is-injective-Fin {zero-ℕ} {succ-ℕ l} e = ex-falso (map-inv-equiv e zero-Fin)
  is-injective-Fin {succ-ℕ k} {zero-ℕ} e = ex-falso (map-equiv e zero-Fin)
  is-injective-Fin {succ-ℕ k} {succ-ℕ l} e =
    ap succ-ℕ (is-injective-Fin (equiv-equiv-Maybe e))

abstract
  double-counting-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
    (count-B : count B) (e : A ≃ B) →
    Id (number-of-elements-count count-A) (number-of-elements-count count-B)
  double-counting-equiv (pair k f) (pair l g) e =
    is-injective-Fin ((inv-equiv g ∘e e) ∘e f)

abstract
  double-counting :
    {l : Level} {A : UU l} (count-A count-A' : count A) →
    Id (number-of-elements-count count-A) (number-of-elements-count count-A')
  double-counting count-A count-A' =
    double-counting-equiv count-A count-A' id-equiv

-- Some immediate corollaries and bureacracy

-- Maybe X has a count if and only if X has a count

count-Maybe : {l : Level} {X : UU l} → count X → count (Maybe X)
count-Maybe {l} {X} e = count-coprod e count-unit

abstract
  is-nonzero-number-of-elements-count-Maybe :
    {l : Level} {X : UU l} (e : count (Maybe X)) →
    is-nonzero-ℕ (number-of-elements-count e)
  is-nonzero-number-of-elements-count-Maybe e p =
    is-empty-is-zero-number-of-elements-count e p exception-Maybe

is-successor-number-of-elements-count-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-successor-ℕ (number-of-elements-count e)
is-successor-number-of-elements-count-Maybe e =
  is-successor-is-nonzero-ℕ (is-nonzero-number-of-elements-count-Maybe e)

count-count-Maybe :
  {l : Level} {X : UU l} → count (Maybe X) → count X
count-count-Maybe (pair k e) with
  is-successor-number-of-elements-count-Maybe (pair k e)
... | pair l refl = pair l (equiv-equiv-Maybe e)

-- Double counting in several specific situations

abstract
  double-counting-coprod :
    { l1 l2 : Level} {A : UU l1} {B : UU l2}
    ( count-A : count A) (count-B : count B) (count-C : count (coprod A B)) →
    Id ( number-of-elements-count count-C)
       ( add-ℕ
         ( number-of-elements-count count-A)
         ( number-of-elements-count count-B))
  double-counting-coprod count-A count-B count-C =
    ( double-counting count-C (count-coprod count-A count-B)) ∙
    ( number-of-elements-count-coprod count-A count-B)

abstract
  double-counting-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) →
    Id ( number-of-elements-count count-C)
       ( sum-count-ℕ count-A (λ x → number-of-elements-count (count-B x)))
  double-counting-Σ count-A count-B count-C =
    ( double-counting count-C (count-Σ count-A count-B)) ∙
    ( number-of-elements-count-Σ count-A count-B)

abstract
  sum-number-of-elements-count-fiber-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
    (f : count (Σ A B)) →
    Id ( sum-count-ℕ e
         ( λ x → number-of-elements-count (count-fiber-count-Σ e f x)))
       ( number-of-elements-count f)
  sum-number-of-elements-count-fiber-count-Σ e f =
    ( inv (number-of-elements-count-Σ e (λ x → count-fiber-count-Σ e f x))) ∙
    ( double-counting (count-Σ e (λ x → count-fiber-count-Σ e f x)) f)

abstract
  double-counting-fiber-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) (x : A) →
    Id ( number-of-elements-count (count-B x))
       ( number-of-elements-count (count-fiber-count-Σ count-A count-C x))
  double-counting-fiber-count-Σ count-A count-B count-C x =
    double-counting (count-B x) (count-fiber-count-Σ count-A count-C x)

abstract
  sum-number-of-elements-count-fib :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (count-A : count A) (count-B : count B) →
    Id ( sum-count-ℕ count-B
         ( λ x → number-of-elements-count (count-fib f count-A count-B x)))
       ( number-of-elements-count count-A)
  sum-number-of-elements-count-fib f count-A count-B =
    sum-number-of-elements-count-fiber-count-Σ count-B
      ( count-equiv' (equiv-total-fib f) count-A)

abstract
  double-counting-fib :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (count-A : count A) →
    (count-B : count B) (count-fib-f : (y : B) → count (fib f y)) (y : B) →
    Id ( number-of-elements-count (count-fib-f y))
       ( number-of-elements-count (count-fib f count-A count-B y))
  double-counting-fib f count-A count-B count-fib-f y =
    double-counting (count-fib-f y) (count-fib f count-A count-B y)

abstract
  sum-number-of-elements-count-base-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    (count-ΣAB : count (Σ A B)) (count-B : (x : A) → count (B x)) →
    Id ( sum-count-ℕ
         ( count-base-count-Σ b count-ΣAB count-B)
         ( λ x → number-of-elements-count (count-B x)))
       ( number-of-elements-count count-ΣAB)
  sum-number-of-elements-count-base-count-Σ b count-ΣAB count-B =
    ( inv
      ( number-of-elements-count-Σ
        ( count-base-count-Σ b count-ΣAB count-B)
        ( count-B))) ∙
    ( double-counting
      ( count-Σ (count-base-count-Σ b count-ΣAB count-B) count-B)
      ( count-ΣAB))

abstract
  double-counting-base-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    (count-A : count A) (count-B : (x : A) → count (B x))
    (count-ΣAB : count (Σ A B)) →
    Id ( number-of-elements-count (count-base-count-Σ b count-ΣAB count-B))
       ( number-of-elements-count count-A)
  double-counting-base-count-Σ b count-A count-B count-ΣAB =
    double-counting (count-base-count-Σ b count-ΣAB count-B) count-A

abstract
  sum-number-of-elements-count-base-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-ΣAB : count (Σ A B)) →
    ( count-B : (x : A) → count (B x)) →
    ( count-nB :
      count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
    Id ( sum-count-ℕ
         ( count-base-count-Σ' count-ΣAB count-B count-nB)
         ( λ x → number-of-elements-count (count-B x)))
       ( number-of-elements-count count-ΣAB)
  sum-number-of-elements-count-base-count-Σ' count-ΣAB count-B count-nB =
    ( inv
      ( number-of-elements-count-Σ
        ( count-base-count-Σ' count-ΣAB count-B count-nB)
        ( count-B))) ∙
    ( double-counting
      ( count-Σ
        ( count-base-count-Σ' count-ΣAB count-B count-nB)
        ( count-B))
      ( count-ΣAB))

abstract
  double-counting-base-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    ( count-B : (x : A) → count (B x)) (count-ΣAB : count (Σ A B)) →
    ( count-nB :
      count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
    Id ( number-of-elements-count
         ( count-base-count-Σ' count-ΣAB count-B count-nB))
       ( number-of-elements-count count-A)
  double-counting-base-count-Σ' count-A count-B count-ΣAB count-nB =
    double-counting (count-base-count-Σ' count-ΣAB count-B count-nB) count-A

abstract
  sum-number-of-elements-coprod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count (coprod A B)) →
    Id ( add-ℕ ( number-of-elements-count (count-left-coprod e))
               ( number-of-elements-count (count-right-coprod e)))
       ( number-of-elements-count e)
  sum-number-of-elements-coprod e =
    ( inv
      ( number-of-elements-count-coprod
        ( count-left-coprod e)
        ( count-right-coprod e))) ∙
    ( inv
      ( double-counting-coprod (count-left-coprod e) (count-right-coprod e) e))

abstract
  product-number-of-elements-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-AB : count (A × B)) →
    (a : A) (b : B) →
    Id ( mul-ℕ ( number-of-elements-count (count-left-factor count-AB b))
               ( number-of-elements-count (count-right-factor count-AB a)))
       ( number-of-elements-count count-AB)
  product-number-of-elements-prod count-AB a b =
    ( inv
      ( number-of-elements-count-prod
        ( count-left-factor count-AB b)
        ( count-right-factor count-AB a))) ∙
    ( double-counting
      ( count-prod
        ( count-left-factor count-AB b)
        ( count-right-factor count-AB a))
      ( count-AB))

--------------------------------------------------------------------------------

-- Section 16.3 Finite types

-- Definition 16.3.1

is-finite-Prop :
  {l : Level} → UU l → UU-Prop l
is-finite-Prop X = trunc-Prop (count X)

is-finite :
  {l : Level} → UU l → UU l
is-finite X = type-Prop (is-finite-Prop X)

abstract
  is-prop-is-finite :
    {l : Level} (X : UU l) → is-prop (is-finite X)
  is-prop-is-finite X = is-prop-type-Prop (is-finite-Prop X)

abstract
  is-finite-count :
    {l : Level} {X : UU l} → count X → is-finite X
  is-finite-count = unit-trunc-Prop

𝔽 : UU (lsuc lzero)
𝔽 = Σ (UU lzero) is-finite

type-𝔽 : 𝔽 → UU lzero
type-𝔽 X = pr1 X

abstract
  is-finite-type-𝔽 : (X : 𝔽) → is-finite (type-𝔽 X)
  is-finite-type-𝔽 X = pr2 X

mere-equiv-Prop :
  {l1 l2 : Level} → UU l1 → UU l2 → UU-Prop (l1 ⊔ l2)
mere-equiv-Prop X Y = trunc-Prop (X ≃ Y)

mere-equiv :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
mere-equiv X Y = type-Prop (mere-equiv-Prop X Y)

abstract
  is-prop-mere-equiv :
    {l1 l2 : Level} (X : UU l1) (Y : UU l2) → is-prop (mere-equiv X Y)
  is-prop-mere-equiv X Y = is-prop-type-Prop (mere-equiv-Prop X Y)

abstract
  refl-mere-equiv :
    {l1 : Level} (X : UU l1) → mere-equiv X X
  refl-mere-equiv X = unit-trunc-Prop id-equiv

abstract
  symmetric-mere-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → mere-equiv X Y → mere-equiv Y X
  symmetric-mere-equiv {l1} {l2} {X} {Y} =
    map-universal-property-trunc-Prop
      ( mere-equiv-Prop Y X)
      ( λ e → unit-trunc-Prop (inv-equiv e))

abstract
  transitive-mere-equiv :
    {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3} →
    mere-equiv X Y → mere-equiv Y Z → mere-equiv X Z
  transitive-mere-equiv {X = X} {Y} {Z} e f =
    apply-universal-property-trunc-Prop e
      ( mere-equiv-Prop X Z)
      ( λ e' →
        apply-universal-property-trunc-Prop f
          ( mere-equiv-Prop X Z)
          ( λ f' → unit-trunc-Prop (f' ∘e e')))

has-cardinality-Prop :
  {l : Level} → UU l → ℕ → UU-Prop l
has-cardinality-Prop X k = mere-equiv-Prop (Fin k) X

has-cardinality :
  {l : Level} → UU l → ℕ → UU l
has-cardinality X k = mere-equiv (Fin k) X

UU-Fin-Level : (l : Level) → ℕ → UU (lsuc l)
UU-Fin-Level l k = Σ (UU l) (mere-equiv (Fin k))

type-UU-Fin-Level : {l : Level} {k : ℕ} → UU-Fin-Level l k → UU l
type-UU-Fin-Level X = pr1 X

abstract
  mere-equiv-UU-Fin-Level :
    {l : Level} {k : ℕ} (X : UU-Fin-Level l k) →
    mere-equiv (Fin k) (type-UU-Fin-Level X)
  mere-equiv-UU-Fin-Level X = pr2 X

UU-Fin : ℕ → UU (lsuc lzero)
UU-Fin k = UU-Fin-Level lzero k

type-UU-Fin : {k : ℕ} → UU-Fin k → UU lzero
type-UU-Fin X = pr1 X

-- Remark 16.3.2

abstract
  is-finite-empty : is-finite empty
  is-finite-empty = is-finite-count count-empty

abstract
  is-finite-is-empty :
    {l1 : Level} {X : UU l1} → is-empty X → is-finite X
  is-finite-is-empty H = is-finite-count (count-is-empty H)

empty-𝔽 : 𝔽
pr1 empty-𝔽 = empty
pr2 empty-𝔽 = is-finite-is-empty id

empty-UU-Fin : UU-Fin zero-ℕ
pr1 empty-UU-Fin = empty
pr2 empty-UU-Fin = unit-trunc-Prop id-equiv

abstract
  is-finite-unit : is-finite unit
  is-finite-unit = is-finite-count count-unit

unit-𝔽 : 𝔽
pr1 unit-𝔽 = unit
pr2 unit-𝔽 = is-finite-unit

unit-UU-Fin : UU-Fin one-ℕ
pr1 unit-UU-Fin = unit
pr2 unit-UU-Fin = unit-trunc-Prop (left-unit-law-coprod unit)

abstract
  is-finite-is-contr :
    {l1 : Level} {X : UU l1} → is-contr X → is-finite X
  is-finite-is-contr H = is-finite-count (count-is-contr H)

abstract
  is-finite-is-decidable-Prop :
    {l : Level} (P : UU-Prop l) →
    is-decidable (type-Prop P) → is-finite (type-Prop P)
  is-finite-is-decidable-Prop P (inl x) =
    is-finite-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) x)
  is-finite-is-decidable-Prop P (inr x) =
    is-finite-is-empty x

abstract
  is-finite-Fin : {k : ℕ} → is-finite (Fin k)
  is-finite-Fin {k} = is-finite-count (count-Fin k)

Fin-𝔽 : ℕ → 𝔽
pr1 (Fin-𝔽 k) = Fin k
pr2 (Fin-𝔽 k) = is-finite-Fin

Fin-UU-Fin : (k : ℕ) → UU-Fin k
pr1 (Fin-UU-Fin k) = Fin k
pr2 (Fin-UU-Fin k) = unit-trunc-Prop id-equiv

raise-Fin : (l : Level) (k : ℕ) → UU l
raise-Fin l k = raise l (Fin k)

equiv-raise-Fin : (l : Level) (k : ℕ) → Fin k ≃ raise-Fin l k
equiv-raise-Fin l k = equiv-raise l (Fin k)

map-raise-Fin : (l : Level) (k : ℕ) → Fin k → raise-Fin l k
map-raise-Fin l k = map-raise

Fin-UU-Fin-Level : (l : Level) (k : ℕ) → UU-Fin-Level l k
pr1 (Fin-UU-Fin-Level l k) = raise-Fin l k
pr2 (Fin-UU-Fin-Level l k) = unit-trunc-Prop (equiv-raise-Fin l k)

abstract
  is-finite-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-finite A → is-finite B
  is-finite-equiv e =
    map-universal-property-trunc-Prop
      ( is-finite-Prop _)
      ( is-finite-count ∘ (count-equiv e))

abstract
  is-finite-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-finite A → is-finite B
  is-finite-is-equiv is-equiv-f =
    map-universal-property-trunc-Prop
      ( is-finite-Prop _)
      ( is-finite-count ∘ (count-equiv (pair _ is-equiv-f)))

abstract
  is-finite-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-finite B → is-finite A
  is-finite-equiv' e = is-finite-equiv (inv-equiv e)

abstract
  is-finite-mere-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
    is-finite A → is-finite B
  is-finite-mere-equiv e H =
    apply-universal-property-trunc-Prop e
      ( is-finite-Prop _)
      ( λ e' → is-finite-equiv e' H)

abstract
  is-finite-type-UU-Fin-Level :
    {l : Level} {k : ℕ} (X : UU-Fin-Level l k) → is-finite (type-UU-Fin-Level X)
  is-finite-type-UU-Fin-Level X =
    is-finite-mere-equiv
      ( mere-equiv-UU-Fin-Level X)
      ( is-finite-Fin)

abstract
  is-finite-type-UU-Fin :
    {k : ℕ} (X : UU-Fin k) → is-finite (type-UU-Fin X)
  is-finite-type-UU-Fin X = is-finite-type-UU-Fin-Level X

abstract
  is-set-is-finite :
    {l : Level} {X : UU l} → is-finite X → is-set X
  is-set-is-finite {l} {X} H =
    apply-universal-property-trunc-Prop H
      ( is-set-Prop X)
      ( λ e → is-set-count e)

abstract
  is-prop-is-inhabited :
    {l1 : Level} {X : UU l1} → (X → is-prop X) → is-prop X
  is-prop-is-inhabited f x y = f x x y

abstract
  is-prop-has-decidable-equality :
    {l1 : Level} {X : UU l1} → is-prop (has-decidable-equality X)
  is-prop-has-decidable-equality {l1} {X} =
    is-prop-is-inhabited
      ( λ d →
        is-prop-Π
        ( λ x →
          is-prop-Π
          ( λ y →
            is-prop-coprod
            ( intro-dn)
            ( is-set-has-decidable-equality d x y)
            ( is-prop-neg))))

has-decidable-equality-Prop :
  {l1 : Level} (X : UU l1) → UU-Prop l1
pr1 (has-decidable-equality-Prop X) = has-decidable-equality X
pr2 (has-decidable-equality-Prop X) = is-prop-has-decidable-equality

has-decidable-equality-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → has-decidable-equality X
has-decidable-equality-is-finite {l1} {X} is-finite-X =
  apply-universal-property-trunc-Prop is-finite-X
    ( has-decidable-equality-Prop X)
    ( λ e →
      has-decidable-equality-equiv' (equiv-count e) has-decidable-equality-Fin)

has-decidable-equality-has-cardinality :
  {l1 : Level} {X : UU l1} {k : ℕ} →
  has-cardinality X k → has-decidable-equality X
has-decidable-equality-has-cardinality {l1} {X} {k} H =
  apply-universal-property-trunc-Prop H
    ( has-decidable-equality-Prop X)
    ( λ e → has-decidable-equality-equiv' e has-decidable-equality-Fin)

abstract
  is-finite-eq :
    {l1 : Level} {X : UU l1} →
    has-decidable-equality X → {x y : X} → is-finite (Id x y)
  is-finite-eq d {x} {y} = is-finite-count (count-eq d x y)

Id-𝔽 : (X : 𝔽) (x y : type-𝔽 X) → 𝔽
pr1 (Id-𝔽 X x y) = Id x y
pr2 (Id-𝔽 X x y) =
  is-finite-eq (has-decidable-equality-is-finite (is-finite-type-𝔽 X))

-- Theorem 16.3.3

abstract
  mere-equiv-UU-Fin :
    {k : ℕ} (X : UU-Fin k) → mere-equiv (Fin k) (type-UU-Fin X)
  mere-equiv-UU-Fin X = pr2 X

has-finite-cardinality :
  {l : Level} → UU l → UU l
has-finite-cardinality X = Σ ℕ (has-cardinality X)

number-of-elements-has-finite-cardinality :
  {l : Level} {X : UU l} → has-finite-cardinality X → ℕ
number-of-elements-has-finite-cardinality = pr1

abstract
  mere-equiv-has-finite-cardinality :
    {l : Level} {X : UU l} (c : has-finite-cardinality X) →
    type-trunc-Prop (Fin (number-of-elements-has-finite-cardinality c) ≃ X)
  mere-equiv-has-finite-cardinality = pr2

abstract
  all-elements-equal-has-finite-cardinality :
    {l1 : Level} {X : UU l1} → all-elements-equal (has-finite-cardinality X)
  all-elements-equal-has-finite-cardinality {l1} {X} (pair k K) (pair l L) =
    eq-subtype
      ( λ k → is-prop-type-trunc-Prop)
      ( apply-universal-property-trunc-Prop K
        ( pair (Id k l) (is-set-ℕ k l))
        ( λ (e : Fin k ≃ X) →
          apply-universal-property-trunc-Prop L
            ( pair (Id k l) (is-set-ℕ k l))
            ( λ (f : Fin l ≃ X) → is-injective-Fin ((inv-equiv f) ∘e e))))

abstract
  is-prop-has-finite-cardinality :
    {l1 : Level} {X : UU l1} → is-prop (has-finite-cardinality X)
  is-prop-has-finite-cardinality =
    is-prop-all-elements-equal all-elements-equal-has-finite-cardinality

has-finite-cardinality-Prop :
  {l1 : Level} (X : UU l1) → UU-Prop l1
pr1 (has-finite-cardinality-Prop X) = has-finite-cardinality X
pr2 (has-finite-cardinality-Prop X) = is-prop-has-finite-cardinality

module _
  {l : Level} {X : UU l}
  where

  abstract
    is-finite-has-finite-cardinality : has-finite-cardinality X → is-finite X
    is-finite-has-finite-cardinality (pair k K) =
      apply-universal-property-trunc-Prop K
        ( is-finite-Prop X)
        ( is-finite-count ∘ (pair k))

  abstract
    is-finite-has-cardinality : {k : ℕ} → has-cardinality X k → is-finite X
    is-finite-has-cardinality {k} H =
      is-finite-has-finite-cardinality (pair k H)

  has-finite-cardinality-count : count X → has-finite-cardinality X
  pr1 (has-finite-cardinality-count e) = number-of-elements-count e
  pr2 (has-finite-cardinality-count e) = unit-trunc-Prop (equiv-count e)

  abstract
    has-finite-cardinality-is-finite : is-finite X → has-finite-cardinality X
    has-finite-cardinality-is-finite =
      map-universal-property-trunc-Prop
        ( has-finite-cardinality-Prop X)
        ( has-finite-cardinality-count)

  number-of-elements-is-finite : is-finite X → ℕ
  number-of-elements-is-finite =
    number-of-elements-has-finite-cardinality ∘ has-finite-cardinality-is-finite

  abstract
    mere-equiv-is-finite :
      (f : is-finite X) → mere-equiv (Fin (number-of-elements-is-finite f)) X
    mere-equiv-is-finite f =
      mere-equiv-has-finite-cardinality (has-finite-cardinality-is-finite f)

  abstract
    compute-number-of-elements-is-finite :
      (e : count X) (f : is-finite X) →
      Id (number-of-elements-count e) (number-of-elements-is-finite f)
    compute-number-of-elements-is-finite e f =
      ind-trunc-Prop
        ( λ g → Id-Prop ℕ-Set ( number-of-elements-count e)
                              ( number-of-elements-is-finite g))
        ( λ g →
          ( is-injective-Fin ((inv-equiv (equiv-count g)) ∘e (equiv-count e))) ∙
          ( ap pr1
            ( eq-is-prop' is-prop-has-finite-cardinality
              ( has-finite-cardinality-count g)
              ( has-finite-cardinality-is-finite (unit-trunc-Prop g)))))
        ( f)

-- Some immediate conclusions of Theorem 16.3.3

has-finite-cardinality-empty : has-finite-cardinality empty
pr1 has-finite-cardinality-empty = zero-ℕ
pr2 has-finite-cardinality-empty = unit-trunc-Prop id-equiv

has-finite-cardinality-is-empty :
  {l1 : Level} {X : UU l1} → is-empty X → has-finite-cardinality X
pr1 (has-finite-cardinality-is-empty f) = zero-ℕ
pr2 (has-finite-cardinality-is-empty f) =
  unit-trunc-Prop (equiv-count (count-is-empty f))

abstract
  is-empty-is-zero-number-of-elements-is-finite :
    {l1 : Level} {X : UU l1} (f : is-finite X) →
    is-zero-ℕ (number-of-elements-is-finite f) → is-empty X
  is-empty-is-zero-number-of-elements-is-finite {l1} {X} f p =
    apply-universal-property-trunc-Prop f
      ( is-empty-Prop X)
      ( λ e →
        is-empty-is-zero-number-of-elements-count e
          ( compute-number-of-elements-is-finite e f ∙ p))

-- Corollary 16.3.4

map-compute-total-UU-Fin : Σ ℕ UU-Fin → 𝔽
pr1 (map-compute-total-UU-Fin (pair k (pair X e))) = X
pr2 (map-compute-total-UU-Fin (pair k (pair X e))) =
  is-finite-has-finite-cardinality (pair k e)

compute-total-UU-Fin : Σ ℕ UU-Fin ≃ 𝔽
compute-total-UU-Fin =
  ( equiv-tot
    ( λ X →
      equiv-prop
        ( is-prop-has-finite-cardinality)
        ( is-prop-is-finite X)
        ( is-finite-has-finite-cardinality)
        ( has-finite-cardinality-is-finite))) ∘e
  ( equiv-left-swap-Σ)

-- Proposition 16.3.5

abstract
  finite-choice-Fin :
    {l1 : Level} {k : ℕ} {Y : Fin k → UU l1} →
    ((x : Fin k) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : Fin k) → Y x)
  finite-choice-Fin {l1} {zero-ℕ} {Y} H = unit-trunc-Prop ind-empty
  finite-choice-Fin {l1} {succ-ℕ k} {Y} H =
    map-inv-equiv-trunc-Prop
      ( equiv-dependent-universal-property-coprod Y)
      ( map-inv-distributive-trunc-prod-Prop
        ( pair
          ( finite-choice-Fin (λ x → H (inl x)))
          ( map-inv-equiv-trunc-Prop
            ( equiv-dependent-universal-property-unit (Y ∘ inr))
            ( H (inr star)))))

abstract
  finite-choice-count :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → count X →
    ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
  finite-choice-count {l1} {l2} {X} {Y} (pair k e) H =
    map-inv-equiv-trunc-Prop
      ( equiv-precomp-Π e Y)
      ( finite-choice-Fin (λ x → H (map-equiv e x)))

abstract
  finite-choice :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → is-finite X →
    ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
  finite-choice {l1} {l2} {X} {Y} is-finite-X H =
    apply-universal-property-trunc-Prop is-finite-X
      ( trunc-Prop ((x : X) → Y x))
      ( λ e → finite-choice-count e H)

-- Remarks

-- Ordering relation on any type A that comes equipped with a count

leq-count :
  {l : Level} {X : UU l} → count X → X → X → UU lzero
leq-count e x y =
  leq-Fin (map-inv-equiv-count e x) (map-inv-equiv-count e y)

refl-leq-count :
  {l : Level} {X : UU l} (e : count X) (x : X) → leq-count e x x
refl-leq-count (pair k e) x = refl-leq-Fin (map-inv-equiv e x)

antisymmetric-leq-count :
  {l : Level} {X : UU l} (e : count X) {x y : X} →
  leq-count e x y → leq-count e y x → Id x y
antisymmetric-leq-count (pair k e) H K =
  is-injective-map-inv-equiv e (antisymmetric-leq-Fin H K)

transitive-leq-count :
  {l : Level} {X : UU l} (e : count X) {x y z : X} →
  leq-count e x y → leq-count e y z → leq-count e x z
transitive-leq-count (pair k e) {x} {y} {z} H K =
  transitive-leq-Fin {x = map-inv-equiv e x} {map-inv-equiv e y} H K

preserves-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X)
  {x y : Fin (number-of-elements-count e)} →
  leq-Fin x y → leq-count e (map-equiv-count e x) (map-equiv-count e y)
preserves-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( isretr-map-inv-equiv (equiv-count e) x)
    ( H)
    ( inv (isretr-map-inv-equiv (equiv-count e) y))

reflects-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X)
  {x y : Fin (number-of-elements-count e)} →
  leq-count e (map-equiv-count e x) (map-equiv-count e y) → leq-Fin x y
reflects-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( inv (isretr-map-inv-equiv (equiv-count e) x))
    ( H)
    ( isretr-map-inv-equiv (equiv-count e) y)

transpose-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X) →
  {x : Fin (number-of-elements-count e)} {y : X} →
  leq-Fin x (map-inv-equiv-count e y) → leq-count e (map-equiv-count e x) y
transpose-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( isretr-map-inv-equiv (equiv-count e) x)
    ( H)
    ( refl)

transpose-leq-equiv-count' :
  {l : Level} {X : UU l} (e : count X) →
  {x : X} {y : Fin (number-of-elements-count e)} →
  leq-Fin (map-inv-equiv-count e x) y → leq-count e x (map-equiv-count e y)
transpose-leq-equiv-count' e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( refl)
    ( H)
    ( inv (isretr-map-inv-equiv (equiv-count e) y))

-- Theorem 16.3.6

-- Theorem 16.3.6 (i)

abstract
  is-finite-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (coprod X Y)
  is-finite-coprod {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (coprod X Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (coprod X Y))
          ( is-finite-count ∘ (count-coprod e)))

coprod-𝔽 : 𝔽 → 𝔽 → 𝔽
pr1 (coprod-𝔽 X Y) = coprod (type-𝔽 X) (type-𝔽 Y)
pr2 (coprod-𝔽 X Y) = is-finite-coprod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y)

abstract
  is-finite-left-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (coprod X Y) →
    is-finite X
  is-finite-left-coprod =
    functor-trunc-Prop count-left-coprod

abstract
  is-finite-right-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (coprod X Y) →
    is-finite Y
  is-finite-right-coprod =
    functor-trunc-Prop count-right-coprod

coprod-UU-Fin-Level :
  {l1 l2 : Level} {k l : ℕ} → UU-Fin-Level l1 k → UU-Fin-Level l2 l →
  UU-Fin-Level (l1 ⊔ l2) (add-ℕ k l)
pr1 (coprod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) = coprod X Y
pr2 (coprod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (add-ℕ k l)) (coprod X Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (add-ℕ k l)) (coprod X Y))
        ( λ e2 →
          unit-trunc-Prop
            ( equiv-coprod e1 e2 ∘e inv-equiv (coprod-Fin k l))))

coprod-UU-Fin :
  {k l : ℕ} → UU-Fin k → UU-Fin l → UU-Fin (add-ℕ k l)
coprod-UU-Fin X Y = coprod-UU-Fin-Level X Y

-- Theorem 16.3.6 (ii)

abstract
  is-finite-prod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (X × Y)
  is-finite-prod {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (X × Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (X × Y))
          ( is-finite-count ∘ (count-prod e)))

prod-𝔽 : 𝔽 → 𝔽 → 𝔽
pr1 (prod-𝔽 X Y) = prod (type-𝔽 X) (type-𝔽 Y)
pr2 (prod-𝔽 X Y) = is-finite-prod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y)

abstract
  is-finite-left-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → Y → is-finite X
  is-finite-left-factor f y =
    functor-trunc-Prop (λ e → count-left-factor e y) f

abstract
  is-finite-right-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → X → is-finite Y
  is-finite-right-factor f x =
    functor-trunc-Prop (λ e → count-right-factor e x) f

prod-UU-Fin-Level :
  {l1 l2 : Level} {k l : ℕ} → UU-Fin-Level l1 k → UU-Fin-Level l2 l →
  UU-Fin-Level (l1 ⊔ l2) (mul-ℕ k l)
pr1 (prod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) = X × Y
pr2 (prod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (mul-ℕ k l)) (X × Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (mul-ℕ k l)) (X × Y))
        ( λ e2 →
          unit-trunc-Prop (equiv-prod e1 e2 ∘e inv-equiv (prod-Fin k l))))

prod-UU-Fin :
  {k l : ℕ} → UU-Fin k → UU-Fin l → UU-Fin (mul-ℕ k l)
prod-UU-Fin = prod-UU-Fin-Level

-- Theorem 16.3.6 (iii)

-- Theorem 16.3.6 (iii) (a) and (b) implies (c)

abstract
  is-finite-Σ :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
    is-finite X → ((x : X) → is-finite (Y x)) → is-finite (Σ X Y)
  is-finite-Σ {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (Σ X Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop
          ( finite-choice is-finite-X is-finite-Y)
          ( is-finite-Prop (Σ X Y))
          ( is-finite-count ∘ (count-Σ e)))

Σ-𝔽 : (X : 𝔽) (Y : type-𝔽 X → 𝔽) → 𝔽
pr1 (Σ-𝔽 X Y) = Σ (type-𝔽 X) (λ x → type-𝔽 (Y x))
pr2 (Σ-𝔽 X Y) =
  is-finite-Σ
    ( is-finite-type-𝔽 X)
    ( λ x → is-finite-type-𝔽 (Y x))

-- Theorem 16.3.6 (iii) (a) and (c) implies (b)

abstract
  is-finite-fiber-is-finite-Σ :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
    is-finite X → is-finite (Σ X Y) → (x : X) → is-finite (Y x)
  is-finite-fiber-is-finite-Σ {l1} {l2} {X} {Y} f g x =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop (Y x))
      ( λ e → functor-trunc-Prop (λ h → count-fiber-count-Σ e h x) g)

-- Theorem 16.3.6 (iii) (b), (c), B has a section implies (a)

abstract
  is-finite-base-is-finite-Σ-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
  is-finite-base-is-finite-Σ-section {l1} {l2} {A} {B} b f g =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop A)
      ( λ e →
        is-finite-count
          ( count-equiv
            ( ( equiv-total-fib-map-section b) ∘e
              ( equiv-tot
                ( λ t →
                  ( equiv-tot (λ x → equiv-eq-pair-Σ (map-section b x) t)) ∘e
                  ( ( assoc-Σ A
                      ( λ (x : A) → Id x (pr1 t))
                      ( λ s → Id (tr B (pr2 s) (b (pr1 s))) (pr2 t))) ∘e
                    ( inv-left-unit-law-Σ-is-contr
                      ( is-contr-total-path' (pr1 t))
                      ( pair (pr1 t) refl))))))
            ( count-Σ e
              ( λ t →
                count-eq
                  ( has-decidable-equality-is-finite (g (pr1 t)))
                  ( b (pr1 t))
                  ( pr2 t)))))

abstract
  is-finite-base-is-finite-Σ-mere-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    type-trunc-Prop ((x : A) → B x) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
  is-finite-base-is-finite-Σ-mere-section {l1} {l2} {A} {B} H f g =
    apply-universal-property-trunc-Prop H
      ( is-finite-Prop A)
      ( λ b → is-finite-base-is-finite-Σ-section b f g)

abstract
  global-choice-count :
    {l : Level} {A : UU l} → count A → global-choice A
  global-choice-count (pair zero-ℕ e) t =
    ex-falso
      ( is-empty-type-trunc-Prop
        ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
        ( t))
  global-choice-count (pair (succ-ℕ k) e) t = map-equiv e zero-Fin

abstract
  global-choice-decidable-subtype-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) {P : A → UU l2} →
    ((x : A) → is-decidable (P x)) → ((x : A) → is-prop (P x)) →
    global-choice (Σ A P)
  global-choice-decidable-subtype-count e {P} d H =
    global-choice-equiv
      ( equiv-Σ-equiv-base P (equiv-count e))
      ( global-choice-decidable-subtype-Fin
        ( λ x → P (map-equiv-count e x))
        ( λ x → H (map-equiv-count e x))
        ( λ x → d (map-equiv-count e x)))

is-inhabited-or-empty-count :
  {l1 : Level} {A : UU l1} → count A → is-inhabited-or-empty A
is-inhabited-or-empty-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-inhabited-or-empty-count (pair (succ-ℕ k) e) =
  inl (unit-trunc-Prop (map-equiv e zero-Fin))

is-inhabited-or-empty-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-inhabited-or-empty A
is-inhabited-or-empty-is-finite {l1} {A} f =
  apply-universal-property-trunc-Prop f
    ( is-inhabited-or-empty-Prop A)
    ( is-inhabited-or-empty-count)

is-decidable-type-trunc-Prop-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-decidable (type-trunc-Prop A)
is-decidable-type-trunc-Prop-is-finite H =
  map-coprod
    ( id)
    ( map-universal-property-trunc-Prop empty-Prop)
    ( is-inhabited-or-empty-is-finite H)

abstract
  global-choice-emb-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
    ((x : A) → is-decidable (fib (map-emb f) x)) → global-choice B
  global-choice-emb-count e f d t =
    map-equiv-total-fib
      ( map-emb f)
      ( global-choice-decidable-subtype-count e d
        ( is-prop-map-emb f)
        ( functor-trunc-Prop
          ( map-inv-equiv-total-fib (map-emb f))
          ( t)))

count-total-subtype-is-finite-total-subtype :
  {l1 l2 : Level} {A : UU l1} (e : count A) (P : A → UU-Prop l2) →
  is-finite (Σ A (λ x → type-Prop (P x))) → count (Σ A (λ x → type-Prop (P x)))
count-total-subtype-is-finite-total-subtype {l1} {l2} {A} e P f =
  count-decidable-subtype P d e
  where
  d : (x : A) → is-decidable (type-Prop (P x))
  d x =
    apply-universal-property-trunc-Prop f
      ( is-decidable-Prop (P x))
      ( λ g → is-decidable-count-Σ e g x)

count-domain-emb-is-finite-domain-emb :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  is-finite B → count B
count-domain-emb-is-finite-domain-emb e f H =
  count-equiv
    ( equiv-total-fib (map-emb f))
    ( count-total-subtype-is-finite-total-subtype e
      ( λ x → pair (fib (map-emb f) x) (is-prop-map-emb f x))
      ( is-finite-equiv'
        ( equiv-total-fib (map-emb f))
        ( H)))

abstract
  choice-count-Σ-is-finite-fiber :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → count (Σ A B) → ((x : A) → is-finite (B x)) →
    ((x : A) → type-trunc-Prop (B x)) → (x : A) → B x
  choice-count-Σ-is-finite-fiber {l1} {l2} {A} {B} K e g H x =
    global-choice-count
      ( count-domain-emb-is-finite-domain-emb e
        ( emb-fiber-inclusion B K x)
        ( g x))
      ( H x)

abstract
  choice-is-finite-Σ-is-finite-fiber :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
    ((x : A) → type-trunc-Prop (B x)) → type-trunc-Prop ((x : A) → B x)
  choice-is-finite-Σ-is-finite-fiber {l1} {l2} {A} {B} K f g H =
    apply-universal-property-trunc-Prop f
      ( trunc-Prop ((x : A) → B x))
      ( λ e → unit-trunc-Prop (choice-count-Σ-is-finite-fiber K e g H))

abstract
  is-finite-base-is-finite-Σ-merely-inhabited :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → (b : (x : A) → type-trunc-Prop (B x)) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
  is-finite-base-is-finite-Σ-merely-inhabited {l1} {l2} {A} {B} K b f g =
    is-finite-base-is-finite-Σ-mere-section
      ( choice-is-finite-Σ-is-finite-fiber K f g b)
      ( f)
      ( g)

-- Theorem 16.3.6 Immediate corollaries and bureaucracy

abstract
  is-finite-fib :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    is-finite X → is-finite Y → (y : Y) → is-finite (fib f y)
  is-finite-fib f is-finite-X is-finite-Y y =
    apply-universal-property-trunc-Prop
      ( is-finite-X)
      ( is-finite-Prop (fib f y))
      ( λ H →
        apply-universal-property-trunc-Prop
          ( is-finite-Y)
          ( is-finite-Prop (fib f y))
          ( λ K → unit-trunc-Prop (count-fib f H K y)))

fib-𝔽 : (X Y : 𝔽) (f : type-𝔽 X → type-𝔽 Y) → type-𝔽 Y → 𝔽
pr1 (fib-𝔽 X Y f y) = fib f y
pr2 (fib-𝔽 X Y f y) =
  is-finite-fib f (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y) y

abstract
  is-finite-fib-map-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
    (t : Σ A B) → is-finite (fib (map-section b) t)
  is-finite-fib-map-section {l1} {l2} {A} {B} b f g (pair y z) =
    is-finite-equiv'
      ( ( ( left-unit-law-Σ-is-contr
            ( is-contr-total-path' y)
            ( pair y refl)) ∘e
          ( inv-assoc-Σ A
            ( λ x → Id x y)
            ( λ t → Id (tr B (pr2 t) (b (pr1 t))) z))) ∘e
        ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
      ( is-finite-eq (has-decidable-equality-is-finite (g y)))

count-type-trunc-Prop :
  {l1 : Level} {A : UU l1} → count A → count (type-trunc-Prop A)
count-type-trunc-Prop (pair zero-ℕ e) =
  count-is-empty
    ( is-empty-type-trunc-Prop
      ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl))
count-type-trunc-Prop (pair (succ-ℕ k) e) =
  count-is-contr
    ( is-proof-irrelevant-is-prop
      ( is-prop-type-trunc-Prop)
      ( unit-trunc-Prop (map-equiv e zero-Fin)))

abstract
  is-finite-type-trunc-Prop :
    {l1 : Level} {A : UU l1} → is-finite A → is-finite (type-trunc-Prop A)
  is-finite-type-trunc-Prop = functor-trunc-Prop count-type-trunc-Prop

trunc-Prop-𝔽 : 𝔽 → 𝔽
pr1 (trunc-Prop-𝔽 A) = type-trunc-Prop (type-𝔽 A)
pr2 (trunc-Prop-𝔽 A) = is-finite-type-trunc-Prop (is-finite-type-𝔽 A)

complement :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
complement {l1} {l2} {A} B = Σ A (is-empty ∘ B)

abstract
  is-finite-base-is-finite-complement :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-set A →
    is-finite (Σ A B) → (g : (x : A) → is-finite (B x)) →
    is-finite (complement B) → is-finite A
  is-finite-base-is-finite-complement {l1} {l2} {A} {B} K f g h =
    is-finite-equiv
      ( ( right-unit-law-Σ-is-contr
          ( λ x →
            is-proof-irrelevant-is-prop
              ( is-prop-is-inhabited-or-empty (B x))
              ( is-inhabited-or-empty-is-finite (g x)))) ∘e
        ( inv-equiv
          ( left-distributive-Σ-coprod A
            ( λ x → type-trunc-Prop (B x))
            ( λ x → is-empty (B x)))))
      ( is-finite-coprod
        ( is-finite-base-is-finite-Σ-merely-inhabited
          ( is-set-subtype (λ x → is-prop-type-trunc-Prop) K)
          ( λ t → pr2 t)
          ( is-finite-equiv
            ( equiv-right-swap-Σ)
            ( is-finite-Σ
              ( f)
              ( λ x → is-finite-type-trunc-Prop (g (pr1 x)))))
          ( λ x → g (pr1 x)))
        ( h))  

--------------------------------------------------------------------------------

Π-ℕ : (k : ℕ) → (Fin k → ℕ) → ℕ
Π-ℕ zero-ℕ x = one-ℕ
Π-ℕ (succ-ℕ k) x = mul-ℕ (Π-ℕ k (λ i → x (inl i))) (x (inr star))

count-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → count (B x)) → count ((x : Fin k) → B x)
count-Π-Fin {l1} {zero-ℕ} {B} e =
  count-is-contr (dependent-universal-property-empty' B)
count-Π-Fin {l1} {succ-ℕ k} {B} e =
  count-equiv'
    ( equiv-dependent-universal-property-coprod B)
    ( count-prod
      ( count-Π-Fin (λ x → e (inl x)))
      ( count-equiv'
        ( equiv-dependent-universal-property-unit (B ∘ inr))
        ( e (inr star))))

count-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count ((x : A) → B x)
count-Π {l1} {l2} {A} {B} e f =
  count-equiv'
    ( equiv-precomp-Π (equiv-count e) B)
    ( count-Π-Fin (λ x → f (map-equiv-count e x)))

count-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  count A → count B → count (A → B)
count-function-type e f =
  count-Π e (λ x → f)

abstract
  is-finite-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → ((x : A) → is-finite (B x)) → is-finite ((x : A) → B x)
  is-finite-Π {l1} {l2} {A} {B} f g =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop ((x : A) → B x))
      ( λ e →
        apply-universal-property-trunc-Prop
          ( finite-choice f g)
          ( is-finite-Prop ((x : A) → B x))
          ( λ h → unit-trunc-Prop (count-Π e h)))

Π-𝔽 : (A : 𝔽) (B : type-𝔽 A → 𝔽) → 𝔽
pr1 (Π-𝔽 A B) = (x : type-𝔽 A) → type-𝔽 (B x)
pr2 (Π-𝔽 A B) = is-finite-Π (is-finite-type-𝔽 A) (λ x → is-finite-type-𝔽 (B x))

abstract
  is-finite-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (A → B)
  is-finite-function-type f g = is-finite-Π f (λ x → g)

_→-𝔽_ : 𝔽 → 𝔽 → 𝔽
pr1 (A →-𝔽 B) = type-𝔽 A → type-𝔽 B
pr2 (A →-𝔽 B) =
  is-finite-function-type (is-finite-type-𝔽 A) (is-finite-type-𝔽 B)

abstract
  is-finite-≃ :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (A ≃ B)
  is-finite-≃ f g =
    is-finite-Σ
      ( is-finite-function-type f g)
      ( λ h →
        is-finite-prod
          ( is-finite-Σ
            ( is-finite-function-type g f)
            ( λ k →
              is-finite-Π g
                ( λ y → is-finite-eq (has-decidable-equality-is-finite g))))
          ( is-finite-Σ
            ( is-finite-function-type g f)
            ( λ k →
              is-finite-Π f
                ( λ x → is-finite-eq (has-decidable-equality-is-finite f)))))

_≃-𝔽_ : 𝔽 → 𝔽 → 𝔽
pr1 (A ≃-𝔽 B) = type-𝔽 A ≃ type-𝔽 B
pr2 (A ≃-𝔽 B) = is-finite-≃ (is-finite-type-𝔽 A) (is-finite-type-𝔽 B)

Aut-𝔽 : 𝔽 → 𝔽
Aut-𝔽 A = A ≃-𝔽 A

--------------------------------------------------------------------------------

-- A combinatorial proof that finite sums are associative

abstract
  associative-sum-count-ℕ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (f : (x : A) → B x → ℕ) →
    Id ( sum-count-ℕ count-A (λ x → sum-count-ℕ (count-B x) (f x)))
      ( sum-count-ℕ (count-Σ count-A count-B) (ind-Σ f))
  associative-sum-count-ℕ {l1} {l2} {A} {B} count-A count-B f =
    ( ( ap-sum-count-ℕ count-A
        ( λ x →
          inv
          ( number-of-elements-count-Σ
            ( count-B x)
            ( λ y → count-Fin (f x y))))) ∙
      ( inv
        ( number-of-elements-count-Σ count-A
          ( λ x → count-Σ (count-B x) (λ y → count-Fin (f x y)))))) ∙
    ( ( double-counting-equiv
        ( count-Σ count-A (λ x → count-Σ (count-B x) (λ y → count-Fin (f x y))))
        ( count-Σ (count-Σ count-A count-B) (λ x → count-Fin (ind-Σ f x)))
        ( inv-assoc-Σ A B (λ x → Fin (ind-Σ f x)))) ∙
      ( number-of-elements-count-Σ
        ( count-Σ count-A count-B)
        ( λ x → (count-Fin (ind-Σ f x)))))

--------------------------------------------------------------------------------

-- Unital magmas

Magma-UU : (l : Level) → UU (lsuc l)
Magma-UU l = Σ (UU l) (λ A → A → A → A)

type-Magma : {l : Level} → Magma-UU l → UU l
type-Magma M = pr1 M

μ-Magma :
  {l : Level} (M : Magma-UU l) → type-Magma M → type-Magma M → type-Magma M
μ-Magma M = pr2 M

fold-Fin-μ-Magma :
  {l : Level} (M : Magma-UU l) → type-Magma M →
  {k : ℕ} → (Fin k → type-Magma M) → type-Magma M
fold-Fin-μ-Magma M m {zero-ℕ} f = m
fold-Fin-μ-Magma M m {succ-ℕ k} f =
  μ-Magma M (fold-Fin-μ-Magma M m (f ∘ inl)) (f (inr star))

fold-count-μ-Magma' :
  {l1 l2 : Level} (M : Magma-UU l1) → type-Magma M →
  {A : UU l2} {k : ℕ} → (Fin k ≃ A) → (A → type-Magma M) → type-Magma M
fold-count-μ-Magma' M m e f = fold-Fin-μ-Magma M m (f ∘ map-equiv e)

fold-count-μ-Magma :
  {l1 l2 : Level} (M : Magma-UU l1) → type-Magma M →
  {A : UU l2} → count A → (A → type-Magma M) → type-Magma M
fold-count-μ-Magma M m e f = fold-Fin-μ-Magma M m (f ∘ map-equiv-count e)

is-unital-Magma : {l : Level} (M : Magma-UU l) → UU l
is-unital-Magma M =
  Σ ( type-Magma M)
    ( λ e →
      ( (x : type-Magma M) → Id (μ-Magma M e x) x) ×
      ( (x : type-Magma M) → Id (μ-Magma M x e) x))

Unital-Magma-UU : (l : Level) → UU (lsuc l)
Unital-Magma-UU l = Σ (Magma-UU l) is-unital-Magma

magma-Unital-Magma :
  {l : Level} → Unital-Magma-UU l → Magma-UU l
magma-Unital-Magma M = pr1 M
  
is-unital-magma-Unital-Magma :
  {l : Level} (M : Unital-Magma-UU l) → is-unital-Magma (magma-Unital-Magma M)
is-unital-magma-Unital-Magma M = pr2 M

is-semigroup-Magma : {l : Level} → Magma-UU l → UU l
is-semigroup-Magma M =
  (x y z : type-Magma M) →
  Id (μ-Magma M (μ-Magma M x y) z) (μ-Magma M x (μ-Magma M y z))

is-commutative-Magma : {l : Level} → Magma-UU l → UU l
is-commutative-Magma M =
  (x y : type-Magma M) → Id (μ-Magma M x y) (μ-Magma M y x)

is-commutative-monoid-Magma : {l : Level} → Magma-UU l → UU l
is-commutative-monoid-Magma M =
  ((is-semigroup-Magma M) × (is-unital-Magma M)) × (is-commutative-Magma M)

unit-is-commutative-monoid-Magma :
  {l : Level} (M : Magma-UU l) → is-commutative-monoid-Magma M → type-Magma M
unit-is-commutative-monoid-Magma M H = pr1 (pr2 (pr1 H))

swap-with-Fin : {k : ℕ} (x y : Fin k) → Fin k → Fin k
swap-with-Fin {k} x y z
  with has-decidable-equality-Fin x z | has-decidable-equality-Fin y z
... | inl p | d = y
... | inr f | inl q = x
... | inr f | inr g = z


{-
permutation-fold-Fin-μ-is-commutative-monoid-Magma :
  {l1 l2 : Level} (M : Magma-UU l1) (H : is-commutative-monoid-Magma M) →
  {k : ℕ} (e : Fin k ≃ Fin k) (f : Fin k → type-Magma M) →
  Id ( fold-Fin-μ-Magma M
       ( unit-is-commutative-monoid-Magma M H)
       ( f ∘ map-equiv e))
     ( fold-Fin-μ-Magma M (unit-is-commutative-monoid-Magma M H) f)
permutation-fold-Fin-μ-is-commutative-monoid-Magma M H {k} e f = {!!}

is-weakly-constant-map-fold-count-μ-is-commutative-monoid-Magma :
  {l1 l2 : Level} (M : Magma-UU l1) (H : is-commutative-monoid-Magma M)
  {A : UU l2} {k : ℕ} →
  is-weakly-constant-map
    ( fold-count-μ-Magma' M (unit-is-commutative-monoid-Magma M H) {A} {k = k})
is-weakly-constant-map-fold-count-μ-is-commutative-monoid-Magma M H {k} e f = {!!}
-}

--------------------------------------------------------------------------------

-- Exercises

--------------------------------------------------------------------------------

-- Exercise 16.1

is-decidable-fib-retract-has-decidable-equality :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → has-decidable-equality B →
  (i : A → B) → retr i → (b : B) → is-decidable (fib i b)
is-decidable-fib-retract-has-decidable-equality d i (pair r R) b =
  is-decidable-iff
    ( λ (p : Id (i (r b)) b) → pair (r b) p)
    ( λ t → ap (i ∘ r) (inv (pr2 t)) ∙ (ap i (R (pr1 t)) ∙ pr2 t))
    ( d (i (r b)) b)

is-decidable-fib-retract-ℕ :
  {l1 : Level} {A : UU l1} (i : A → ℕ) → retr i → (x : ℕ) →
  is-decidable (fib i x)
is-decidable-fib-retract-ℕ =
  is-decidable-fib-retract-has-decidable-equality has-decidable-equality-ℕ

is-decidable-fib-retract-Fin :
  {l1 : Level} {k : ℕ} {A : UU l1} (i : A → Fin k) → retr i → (x : Fin k) →
  is-decidable (fib i x)
is-decidable-fib-retract-Fin {l1} {k} =
  is-decidable-fib-retract-has-decidable-equality has-decidable-equality-Fin

is-decidable-fib-retract-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) → retr i →
  (y : B) → is-decidable (fib i y)
is-decidable-fib-retract-count e =
  is-decidable-fib-retract-has-decidable-equality
    ( has-decidable-equality-count e)

is-decidable-fib-retract-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : is-finite B) (i : A → B) →
  retr i → (y : B) → is-decidable (fib i y)
is-decidable-fib-retract-is-finite H =
  is-decidable-fib-retract-has-decidable-equality
    ( has-decidable-equality-is-finite H)

abstract
  is-injective-retr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → retr f →
    is-injective f
  is-injective-retr f (pair h H) {x} {y} p = (inv (H x)) ∙ (ap h p ∙ H y)

abstract
  is-emb-retract-count :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) →
    retr i → is-emb i
  is-emb-retract-count e i R =
    is-emb-is-injective (is-set-count e) (is-injective-retr i R)

emb-retract-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) →
  retr i → A ↪ B
pr1 (emb-retract-count e i R) = i
pr2 (emb-retract-count e i R) = is-emb-retract-count e i R

count-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → count B → count A
count-retract (pair i R) e =
  count-equiv
    ( equiv-total-fib i)
    ( count-decidable-subtype
      ( fib-emb-Prop (emb-retract-count e i R))
      ( is-decidable-fib-retract-count e i R)
      ( e))

abstract
  is-finite-retract :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → A retract-of B →
    is-finite B → is-finite A
  is-finite-retract R = functor-trunc-Prop (count-retract R)

-- Exercise 16.2

-- Exercise 16.2 (a)

is-decidable-Π-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : coprod A B → UU l3} →
  is-decidable ((a : A) → C (inl a)) → is-decidable ((b : B) → C (inr b)) →
  is-decidable ((x : coprod A B) → C x)
is-decidable-Π-coprod {C = C} dA dB =
  is-decidable-equiv
    ( equiv-dependent-universal-property-coprod C)
    ( is-decidable-prod dA dB)

is-decidable-Π-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable ((x : A) → B (unit-Maybe x)) → is-decidable (B exception-Maybe) →
  is-decidable ((x : Maybe A) → B x)
is-decidable-Π-Maybe {B = B} du de =
  is-decidable-equiv
    ( equiv-dependent-universal-property-Maybe B)
    ( is-decidable-prod du de)

is-decidable-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → is-decidable (B x)) → is-decidable ((x : Fin k) → B x)
is-decidable-Π-Fin {l1} {zero-ℕ} {B} d = inl ind-empty
is-decidable-Π-Fin {l1} {succ-ℕ k} {B} d =
  is-decidable-Π-Maybe
    ( is-decidable-Π-Fin (λ x → d (inl x)))
    ( d (inr star))

is-decidable-Π-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable ((x : A) → C x) → is-decidable ((y : B) → D y)
is-decidable-Π-equiv {D = D} e f = is-decidable-equiv' (equiv-Π D e f)

is-decidable-Π-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable ((y : B) → D y) → is-decidable ((x : A) → C x)
is-decidable-Π-equiv' {D = D} e f = is-decidable-equiv (equiv-Π D e f)

is-decidable-Π-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → is-decidable (B x)) → is-decidable ((x : A) → B x)
is-decidable-Π-count e d =
  is-decidable-Π-equiv
    ( equiv-count e)
    ( λ x → id-equiv)
    ( is-decidable-Π-Fin (λ x → d (map-equiv-count e x)))

is-decidable-Π-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-finite A →
  ((x : A) → is-decidable (B x)) → is-decidable ((x : A) → B x)
is-decidable-Π-is-finite {l1} {l2} {A} {B} H d =
  is-decidable-iff
    ( map-Π (λ x → elim-trunc-Prop-is-decidable (d x)))
    ( map-Π (λ x → unit-trunc-Prop))
    ( is-decidable-iff
      ( α)
      ( finite-choice H)
      ( apply-universal-property-trunc-Prop H
        ( is-decidable-Prop (trunc-Prop ((x : A) → B x)))
        ( λ e →
          is-decidable-iff
            ( finite-choice H)
            ( α)
            ( is-decidable-Π-count e
              ( λ x →
                is-decidable-iff
                  ( unit-trunc-Prop)
                  ( elim-trunc-Prop-is-decidable (d x))
                  ( d x))))))
  where
  α : type-trunc-Prop ((x : A) → B x) → (x : A) → type-trunc-Prop (B x)
  α = map-universal-property-trunc-Prop
        ( Π-Prop A (λ x → trunc-Prop (B x)))
        ( λ (f : (x : A) → B x) (x : A) → unit-trunc-Prop (f x))

-- Remark: The analogous development for Σ-types stops at is-decidable-Σ-count

is-decidable-Σ-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : coprod A B → UU l3) →
  is-decidable (Σ A (C ∘ inl)) → is-decidable (Σ B (C ∘ inr)) →
  is-decidable (Σ (coprod A B) C)
is-decidable-Σ-coprod {l1} {l2} {l3} {A} {B} C dA dB =
  is-decidable-equiv
    ( right-distributive-Σ-coprod A B C)
    ( is-decidable-coprod dA dB)

is-decidable-Σ-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable (Σ A (B ∘ unit-Maybe)) → is-decidable (B exception-Maybe) →
  is-decidable (Σ (Maybe A) B)
is-decidable-Σ-Maybe {l1} {l2} {A} {B} dA de =
  is-decidable-Σ-coprod B dA
    ( is-decidable-equiv
      ( left-unit-law-Σ (B ∘ inr))
      ( de))

is-decidable-Σ-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable (Σ A C) → is-decidable (Σ B D)
is-decidable-Σ-equiv {D = D} e f =
  is-decidable-equiv' (equiv-Σ D e f)

is-decidable-Σ-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable (Σ B D) → is-decidable (Σ A C)
is-decidable-Σ-equiv' {D = D} e f =
  is-decidable-equiv (equiv-Σ D e f) 

is-decidable-Σ-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count A →
  ((x : A) → is-decidable (B x)) → is-decidable (Σ A B)
is-decidable-Σ-count e d =
  is-decidable-Σ-equiv
    ( equiv-count e)
    ( λ x → id-equiv)
    ( is-decidable-Σ-Fin (λ x → d (map-equiv-count e x)))

-- There is no way to construct a function is-decidable-Σ-is-finite. This would
-- contradict the univalence axiom.

-- Exercise 16.2 (b)

is-decidable-is-injective-is-finite' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable ((x y : A) → Id (f x) (f y) → Id x y)
is-decidable-is-injective-is-finite' f HA HB =
  is-decidable-Π-is-finite HA
    ( λ x →
      is-decidable-Π-is-finite HA
        ( λ y →
          is-decidable-function-type
            ( has-decidable-equality-is-finite HB (f x) (f y))
            ( has-decidable-equality-is-finite HA x y)))

is-decidable-is-injective-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-injective f)
is-decidable-is-injective-is-finite f HA HB =
  is-decidable-iff
    ( λ p {x} {y} → p x y)
    ( λ p x y → p)
    ( is-decidable-is-injective-is-finite' f HA HB)

is-decidable-is-emb-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-emb f)
is-decidable-is-emb-is-finite f HA HB =
  is-decidable-iff
    ( is-emb-is-injective (is-set-is-finite HB))
    ( is-injective-is-emb)
    ( is-decidable-is-injective-is-finite f HA HB)

-- Exercise 16.2 (c)

is-decidable-is-surjective-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-surjective f)
is-decidable-is-surjective-is-finite f HA HB =
  is-decidable-Π-is-finite HB
    ( λ y → is-decidable-type-trunc-Prop-is-finite (is-finite-fib f HA HB y))

-- Exercise 16.2 (d)

is-decidable-is-equiv-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-equiv f)
is-decidable-is-equiv-is-finite f HA HB =
  is-decidable-iff
    ( λ p → is-equiv-is-emb-is-surjective (pr1 p) (pr2 p))
    ( λ K → pair (is-surjective-is-equiv K) (is-emb-is-equiv K))
    ( is-decidable-prod
      ( is-decidable-is-surjective-is-finite f HA HB)
      ( is-decidable-is-emb-is-finite f HA HB))

-- Exercise 16.4

-- Exercise 16.4 (a)

Fin-exp-ℕ : (n m : ℕ) → Fin (exp-ℕ n m) ≃ (Fin m → Fin n)
Fin-exp-ℕ n zero-ℕ =
  equiv-is-contr is-contr-Fin-one-ℕ (universal-property-empty' (Fin n))
Fin-exp-ℕ n (succ-ℕ m) =
  ( ( inv-equiv equiv-universal-property-Maybe) ∘e
    ( equiv-prod (Fin-exp-ℕ n m) id-equiv)) ∘e
  ( Fin-mul-ℕ (exp-ℕ n m) n)

-- Exercise 16.4 (b)

-- The number falling-factorial-ℕ n m is the number (n)_m from combinatorics

falling-factorial-ℕ : ℕ → ℕ → ℕ
falling-factorial-ℕ zero-ℕ zero-ℕ = one-ℕ
falling-factorial-ℕ zero-ℕ (succ-ℕ m) = zero-ℕ
falling-factorial-ℕ (succ-ℕ n) zero-ℕ = one-ℕ
falling-factorial-ℕ (succ-ℕ n) (succ-ℕ m) =
  mul-ℕ (succ-ℕ n) (falling-factorial-ℕ n m)

{-
Fin-falling-factorial-ℕ :
  (n m : ℕ) → Fin (falling-factorial-ℕ n m) ≃ (Fin m ↪ Fin n)
Fin-falling-factorial-ℕ n m = {!!}
-}

{-
Fin-falling-factorial-ℕ : (n m : ℕ) → Fin (falling-factorial-ℕ n m) ≃ (Fin m ↪ Fin n)
Fin-falling-factorial-ℕ zero-ℕ zero-ℕ =
  equiv-is-contr
    ( is-contr-Fin-one-ℕ)
    ( is-contr-equiv
      ( is-emb id)
      ( left-unit-law-Σ-is-contr
        ( universal-property-empty' empty)
        ( id))
      ( dependent-universal-property-empty'
        ( λ x → (y : empty) → is-equiv (ap id))))
Fin-falling-factorial-ℕ zero-ℕ (succ-ℕ m) =
  equiv-is-empty id (λ f → map-emb f (inr star))
Fin-falling-factorial-ℕ (succ-ℕ n) zero-ℕ =
  equiv-is-contr
    ( is-contr-Fin-one-ℕ)
    ( is-contr-equiv
      ( is-emb ex-falso)
      ( left-unit-law-Σ-is-contr
        ( universal-property-empty' (Fin (succ-ℕ n)))
        ( ex-falso))
      ( dependent-universal-property-empty'
        ( λ x → (y : empty) → is-equiv (ap ex-falso))))
Fin-falling-factorial-ℕ (succ-ℕ n) (succ-ℕ m) =
  ( ( ( right-unit-law-Σ-is-contr
        { B = λ f → is-decidable (fib (map-emb f) (inr star))}
        ( λ f →
          is-proof-irrelevant-is-prop
            ( is-prop-is-decidable
              ( is-prop-map-is-emb (is-emb-map-emb f) (inr star)))
            ( is-decidable-Σ-Fin
              ( λ x →
                has-decidable-equality-Fin (map-emb f x) (inr star))))) ∘e
      ( ( inv-equiv
          ( left-distributive-Σ-coprod
            ( Fin (succ-ℕ m) ↪ Fin (succ-ℕ n))
            ( λ f → fib (map-emb f) (inr star))
            ( λ f → ¬ (fib (map-emb f) (inr star))))) ∘e
        {!!})) ∘e
    ( equiv-coprod (Fin-falling-factorial-ℕ n m) (Fin-falling-factorial-ℕ n (succ-ℕ m)))) ∘e
  ( Fin-add-ℕ (falling-factorial-ℕ n m) (falling-factorial-ℕ n (succ-ℕ m)))
-}

-- Exercise 16.4 (d)

stirling-number-second-kind : ℕ → ℕ → ℕ
stirling-number-second-kind zero-ℕ zero-ℕ = one-ℕ
stirling-number-second-kind zero-ℕ (succ-ℕ n) = zero-ℕ
stirling-number-second-kind (succ-ℕ m) zero-ℕ = zero-ℕ
stirling-number-second-kind (succ-ℕ m) (succ-ℕ n) =
  add-ℕ
    ( mul-ℕ (succ-ℕ n) (stirling-number-second-kind m (succ-ℕ n)))
    ( stirling-number-second-kind m n)

-- Exercise 16.8

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (K : is-finite A)
  where

  abstract
    is-finite-codomain :
      is-surjective f → has-decidable-equality B → is-finite B
    is-finite-codomain H d =
      is-finite-base-is-finite-Σ-merely-inhabited
        ( is-set-has-decidable-equality d)
        ( H)
        ( is-finite-equiv' (equiv-total-fib f) K)
        ( λ b → is-finite-Σ K (λ a → is-finite-eq d))

abstract
  is-finite-im :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (K : is-finite A) →
    has-decidable-equality B → is-finite (im f)
  is-finite-im {f = f} K d =
    is-finite-codomain K
      ( is-surjective-map-unit-im f)
      ( λ x y →
        is-decidable-equiv
          ( equiv-Eq-eq-total-subtype (λ u → is-prop-type-trunc-Prop) x y)
          ( d (pr1 x) (pr1 y)))

-- Exercise 16.15

is-inl-Fin : {k : ℕ} → Fin (succ-ℕ k) → UU lzero
is-inl-Fin {k} x = Σ (Fin k) (λ y → Id (inl y) x)

is-star-Fin : {k : ℕ} → Fin (succ-ℕ k) → UU lzero
is-star-Fin x = Id (inr star) x

is-star-is-not-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → ¬ (is-inl-Fin x) → is-star-Fin x
is-star-is-not-inl-Fin (inl x) H = ex-falso (H (pair x refl))
is-star-is-not-inl-Fin (inr star) H = refl

skip-Fin :
  {k : ℕ} → Fin (succ-ℕ k) → Fin k → Fin (succ-ℕ k)
skip-Fin {succ-ℕ k} (inl x) (inl y) = inl (skip-Fin x y)
skip-Fin {succ-ℕ k} (inl x) (inr y) = inr star
skip-Fin {succ-ℕ k} (inr x) y = inl y

abstract
  is-injective-skip-Fin :
    {k : ℕ} (x : Fin (succ-ℕ k)) → is-injective (skip-Fin x)
  is-injective-skip-Fin {succ-ℕ k} (inl x) {inl y} {inl z} p =
    ap ( inl)
       ( is-injective-skip-Fin x
         ( is-injective-is-emb (is-emb-inl (Fin (succ-ℕ k)) unit) p))
  is-injective-skip-Fin {succ-ℕ k} (inl x) {inr star} {inr star} p = refl
  is-injective-skip-Fin {succ-ℕ k} (inr star) {y} {z} p =
    is-injective-is-emb (is-emb-inl (Fin (succ-ℕ k)) unit) p

abstract
  is-emb-skip-Fin :
    {k : ℕ} (x : Fin (succ-ℕ k)) → is-emb (skip-Fin x)
  is-emb-skip-Fin {k} x =
    is-emb-is-injective
      ( is-set-Fin (succ-ℕ k))
      ( is-injective-skip-Fin x)

emb-skip-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → Fin k ↪ Fin (succ-ℕ k)
pr1 (emb-skip-Fin x) = skip-Fin x
pr2 (emb-skip-Fin x) = is-emb-skip-Fin x

repeat-Fin :
  {k : ℕ} (x : Fin k) → Fin (succ-ℕ k) → Fin k
repeat-Fin {succ-ℕ k} (inl x) (inl y) = inl (repeat-Fin x y)
repeat-Fin {succ-ℕ k} (inl x) (inr star) = inr star
repeat-Fin {succ-ℕ k} (inr star) (inl y) = y
repeat-Fin {succ-ℕ k} (inr star) (inr star) = inr star

abstract
  is-almost-injective-repeat-Fin :
    {k : ℕ} (x : Fin k) {y z : Fin (succ-ℕ k)} →
    ¬ (Id (inl x) y) → ¬ (Id (inl x) z) →
    Id (repeat-Fin x y) (repeat-Fin x z) → Id y z
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inl y} {inl z} f g p =
    ap ( inl)
       ( is-almost-injective-repeat-Fin x
         ( λ q → f (ap inl q))
         ( λ q → g (ap inl q))
         ( is-injective-inl p))
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inl y} {inr star} f g p =
    ex-falso (Eq-Fin-eq p)
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inr star} {inl z} f g p =
    ex-falso (Eq-Fin-eq p)
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inl x) {inr star} {inr star} f g p =
    refl
  is-almost-injective-repeat-Fin {succ-ℕ k} (inr star) {inl y} {inl z} f g p =
    ap inl p
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inr star) {inl y} {inr star} f g p =
    ex-falso (f (ap inl (inv p)))
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inr star) {inr star} {inl z} f g p =
    ex-falso (g (ap inl p))
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inr star) {inr star} {inr star} f g p = refl

is-decidable-is-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-decidable (is-inl-Fin x)
is-decidable-is-inl-Fin (inl x) = inl (pair x refl)
is-decidable-is-inl-Fin (inr star) = inr α
  where
  α : is-inl-Fin (inr star) → empty
  α (pair y p) = Eq-Fin-eq p 

cases-map-reduce-emb-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
  is-decidable (is-inl-Fin (map-emb f (inr star))) → (x : Fin k) →
  is-decidable (is-inl-Fin (map-emb f (inl x))) → Fin l
cases-map-reduce-emb-Fin f (inl (pair t p)) x d = repeat-Fin t (map-emb f (inl x))
cases-map-reduce-emb-Fin f (inr g) x (inl (pair y p)) = y
cases-map-reduce-emb-Fin f (inr g) x (inr h) =
  ex-falso (Eq-Fin-eq (is-injective-emb f ((inv p) ∙ q)))
  where
  p : is-star-Fin (map-emb f (inr star))
  p = is-star-is-not-inl-Fin (map-emb f (inr star)) g
  q : is-star-Fin (map-emb f (inl x))
  q = is-star-is-not-inl-Fin (map-emb f (inl x)) h

map-reduce-emb-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) → Fin k → Fin l
map-reduce-emb-Fin f x =
  cases-map-reduce-emb-Fin f
    ( is-decidable-is-inl-Fin (map-emb f (inr star)))
    ( x)
    ( is-decidable-is-inl-Fin (map-emb f (inl x)))

abstract
  is-injective-cases-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l))
    (d : is-decidable (is-inl-Fin (map-emb f (inr star))))
    (x : Fin k) (e : is-decidable (is-inl-Fin (map-emb f (inl x))))
    (x' : Fin k) (e' : is-decidable  (is-inl-Fin (map-emb f (inl x')))) →
    Id (cases-map-reduce-emb-Fin f d x e) (cases-map-reduce-emb-Fin f d x' e') →
    Id x x'
  is-injective-cases-map-reduce-emb-Fin f (inl (pair t q)) x e x' e' p =
    is-injective-inl
      ( is-injective-is-emb
        ( is-emb-map-emb f)
        ( is-almost-injective-repeat-Fin t
          ( λ α → Eq-Fin-eq (is-injective-emb f ((inv q) ∙ α)))
          ( λ α → Eq-Fin-eq (is-injective-emb f ((inv q) ∙ α)))
          ( p)))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inl (pair y q)) x' (inl (pair y' q')) p =
    is-injective-inl (is-injective-emb f ((inv q) ∙ (ap inl p ∙ q')))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inl (pair y q)) x' (inr h) p =
    ex-falso
    ( Eq-Fin-eq
      ( is-injective-emb f
        ( ( inv (is-star-is-not-inl-Fin (pr1 f (inr star)) g)) ∙
          ( is-star-is-not-inl-Fin (pr1 f (inl x')) h))))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inr h) x' (inl (pair y' q')) p =
    ex-falso
      ( Eq-Fin-eq
        ( is-injective-emb f
          ( ( inv (is-star-is-not-inl-Fin (pr1 f (inr star)) g)) ∙
            ( is-star-is-not-inl-Fin (pr1 f (inl x)) h))))
  is-injective-cases-map-reduce-emb-Fin f (inr g) x (inr h) x' (inr k) p =
    ex-falso
      ( Eq-Fin-eq
        ( is-injective-emb f
          ( ( inv (is-star-is-not-inl-Fin (pr1 f (inr star)) g)) ∙
            ( is-star-is-not-inl-Fin (pr1 f (inl x)) h))))

abstract
  is-injective-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-injective (map-reduce-emb-Fin f)
  is-injective-map-reduce-emb-Fin f {x} {y} =
    is-injective-cases-map-reduce-emb-Fin f
      ( is-decidable-is-inl-Fin (map-emb f (inr star)))
      ( x)
      ( is-decidable-is-inl-Fin (map-emb f (inl x)))
      ( y)
      ( is-decidable-is-inl-Fin (map-emb f (inl y)))

abstract
  is-emb-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-emb (map-reduce-emb-Fin f)
  is-emb-map-reduce-emb-Fin f =
    is-emb-is-injective (is-set-Fin _) (is-injective-map-reduce-emb-Fin f)

reduce-emb-Fin :
  (k l : ℕ) → Fin (succ-ℕ k) ↪ Fin (succ-ℕ l) → Fin k ↪ Fin l
pr1 (reduce-emb-Fin k l f) = map-reduce-emb-Fin f
pr2 (reduce-emb-Fin k l f) = is-emb-map-reduce-emb-Fin f

-- We now come to the main result

abstract
  leq-emb-Fin :
    {k l : ℕ} → Fin k ↪ Fin l → k ≤-ℕ l
  leq-emb-Fin {zero-ℕ} {zero-ℕ} f = refl-leq-ℕ zero-ℕ
  leq-emb-Fin {succ-ℕ k} {zero-ℕ} f = ex-falso (map-emb f (inr star))
  leq-emb-Fin {zero-ℕ} {succ-ℕ l} f = leq-zero-ℕ (succ-ℕ l)
  leq-emb-Fin {succ-ℕ k} {succ-ℕ l} f = leq-emb-Fin (reduce-emb-Fin k l f)

abstract
  leq-is-emb-Fin :
    {k l : ℕ} {f : Fin k → Fin l} → is-emb f → k ≤-ℕ l
  leq-is-emb-Fin {f = f} H = leq-emb-Fin (pair f H)

abstract
  leq-is-injective-Fin :
    {k l : ℕ} {f : Fin k → Fin l} → is-injective f → k ≤-ℕ l
  leq-is-injective-Fin H = leq-is-emb-Fin (is-emb-is-injective (is-set-Fin _) H)

abstract
  is-not-emb-le-Fin :
    {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → ¬ (is-emb f)
  is-not-emb-le-Fin {k} {l} f p =
    functor-neg (leq-is-emb-Fin) (contradiction-le-ℕ l k p)

abstract
  is-not-injective-le-Fin :
    {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → is-not-injective f
  is-not-injective-le-Fin {k} {l} f p =
    functor-neg (is-emb-is-injective (is-set-Fin l)) (is-not-emb-le-Fin f p)

abstract
  is-not-injective-map-Fin-succ-Fin :
    {k : ℕ} (f : Fin (succ-ℕ k) → Fin k) → is-not-injective f 
  is-not-injective-map-Fin-succ-Fin {k} f =
    is-not-injective-le-Fin f (le-succ-ℕ {k})

abstract
  no-embedding-ℕ-Fin :
    (k : ℕ) → ¬ (ℕ ↪ Fin k)
  no-embedding-ℕ-Fin k e =
    contradiction-leq-ℕ k k
      ( refl-leq-ℕ k)
      ( leq-emb-Fin (comp-emb e (emb-nat-Fin (succ-ℕ k))))

-- We generalise the main results to types equipped with a counting

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (eA : count A) (eB : count B)
  where

  abstract
    leq-emb-count :
      (A ↪ B) → (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
    leq-emb-count f =
      leq-emb-Fin
        ( comp-emb
          ( comp-emb (emb-equiv (inv-equiv-count eB)) f)
          ( emb-equiv (equiv-count eA)))

  abstract
    leq-is-emb-count :
      {f : A → B} → is-emb f → 
      (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
    leq-is-emb-count {f} H = leq-emb-count (pair f H)

  abstract
    leq-is-injective-count :
      {f : A → B} → is-injective f →
      (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
    leq-is-injective-count H =
      leq-is-emb-count (is-emb-is-injective (is-set-count eB) H)

  abstract
    is-not-emb-le-count :
      (f : A → B) →
      le-ℕ (number-of-elements-count eB) (number-of-elements-count eA) →
      ¬ (is-emb f)
    is-not-emb-le-count f p H =
      is-not-emb-le-Fin (map-emb h) p (is-emb-map-emb h)
      where
      h : Fin (number-of-elements-count eA) ↪ Fin (number-of-elements-count eB)
      h = comp-emb
            ( emb-equiv (inv-equiv-count eB))
            ( comp-emb (pair f H) (emb-equiv (equiv-count eA)))

  abstract
    is-not-injective-le-count :
      (f : A → B) →
      le-ℕ (number-of-elements-count eB) (number-of-elements-count eA) →
      is-not-injective f
    is-not-injective-le-count f p H =
      is-not-emb-le-count f p (is-emb-is-injective (is-set-count eB) H)

abstract
  no-embedding-ℕ-count :
    {l : Level} {A : UU l} (e : count A) → ¬ (ℕ ↪ A)
  no-embedding-ℕ-count e f =
    no-embedding-ℕ-Fin
      ( number-of-elements-count e)
      ( comp-emb (emb-equiv (inv-equiv-count e)) f)

-- We generalise the main results to finite types

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : is-finite A) (K : is-finite B)
  where

  abstract
    leq-emb-is-finite :
      (A ↪ B) →
      (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
    leq-emb-is-finite f =
      apply-universal-property-trunc-Prop H P
        ( λ eA →
          apply-universal-property-trunc-Prop K P
            ( λ eB →
              concatenate-eq-leq-eq-ℕ
                ( inv (compute-number-of-elements-is-finite eA H))
                ( leq-emb-count eA eB f)
                ( compute-number-of-elements-is-finite eB K)))
      where
      P : UU-Prop lzero
      P = leq-ℕ-Prop
            ( number-of-elements-is-finite H)
            ( number-of-elements-is-finite K)

  abstract
    leq-is-emb-is-finite :
      {f : A → B} → is-emb f →
      (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
    leq-is-emb-is-finite {f} H =
      leq-emb-is-finite (pair f H)

  abstract
    leq-is-injective-is-finite :
      {f : A → B} → is-injective f →
      (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
    leq-is-injective-is-finite I =
      leq-is-emb-is-finite (is-emb-is-injective (is-set-is-finite K) I)

  abstract
    is-not-emb-le-is-finite :
      (f : A → B) →
      le-ℕ (number-of-elements-is-finite K) (number-of-elements-is-finite H) →
      ¬ (is-emb f)
    is-not-emb-le-is-finite f p E =
      apply-universal-property-trunc-Prop H empty-Prop
        ( λ e →
          apply-universal-property-trunc-Prop K empty-Prop
            ( λ d → is-not-emb-le-count e d f
              ( concatenate-eq-le-eq-ℕ
                ( compute-number-of-elements-is-finite d K)
                ( p)
                ( inv (compute-number-of-elements-is-finite e H)))
              ( E)))

  abstract
    is-not-injective-le-is-finite :
      (f : A → B) →
      le-ℕ (number-of-elements-is-finite K) (number-of-elements-is-finite H) →
      is-not-injective f
    is-not-injective-le-is-finite f p I =
      is-not-emb-le-is-finite f p (is-emb-is-injective (is-set-is-finite K) I)

abstract
  no-embedding-ℕ-is-finite :
    {l : Level} {A : UU l} (H : is-finite A) → ¬ (ℕ ↪ A)
  no-embedding-ℕ-is-finite H f =
    apply-universal-property-trunc-Prop H empty-Prop
      ( λ e → no-embedding-ℕ-count e f)
```
