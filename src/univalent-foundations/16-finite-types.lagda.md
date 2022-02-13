---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-foundations.16-finite-types where

open import foundation public
open import elementary-number-theory public

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

-- Exercise 16.4 (b)

-- The number falling-factorial-ℕ n m is the number (n)_m from combinatorics

falling-factorial-ℕ : ℕ → ℕ → ℕ
falling-factorial-ℕ zero-ℕ zero-ℕ = 1
falling-factorial-ℕ zero-ℕ (succ-ℕ m) = 0
falling-factorial-ℕ (succ-ℕ n) zero-ℕ = 1
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
stirling-number-second-kind zero-ℕ zero-ℕ = 1
stirling-number-second-kind zero-ℕ (succ-ℕ n) = 0
stirling-number-second-kind (succ-ℕ m) zero-ℕ = 0
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
          ( extensionality-type-subtype (λ u → trunc-Prop (fib f u)) x y)
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
    map-neg (leq-is-emb-Fin) (contradiction-le-ℕ l k p)

abstract
  is-not-injective-le-Fin :
    {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → ¬ (is-injective f)
  is-not-injective-le-Fin {k} {l} f p =
    map-neg (is-emb-is-injective (is-set-Fin l)) (is-not-emb-le-Fin f p)

abstract
  is-not-injective-map-Fin-succ-Fin :
    {k : ℕ} (f : Fin (succ-ℕ k) → Fin k) → ¬ (is-injective f)
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
      ¬ (is-injective f)
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
      ¬ (is-injective f)
    is-not-injective-le-is-finite f p I =
      is-not-emb-le-is-finite f p (is-emb-is-injective (is-set-is-finite K) I)

abstract
  no-embedding-ℕ-is-finite :
    {l : Level} {A : UU l} (H : is-finite A) → ¬ (ℕ ↪ A)
  no-embedding-ℕ-is-finite H f =
    apply-universal-property-trunc-Prop H empty-Prop
      ( λ e → no-embedding-ℕ-count e f)
```
