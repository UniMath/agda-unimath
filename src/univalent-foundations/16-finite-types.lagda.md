---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-foundations.16-finite-types where

open import foundation public
open import elementary-number-theory public

-- Remark: The analogous development for Σ-types stops at is-decidable-Σ-count

-- There is no way to construct a function is-decidable-Σ-is-finite. This would
-- contradict the univalence axiom.

-- Exercise 16.2 (b)

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
