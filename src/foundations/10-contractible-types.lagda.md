---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.10-contractible-types where

import foundations.09-equivalences
open foundations.09-equivalences public

--------------------------------------------------------------------------------

-- Section 10 Contractible types

--------------------------------------------------------------------------------

-- Section 10.1 Contractible types

{- Definition 10.1.1 -}

is-contr :
  {l : Level} → UU l → UU l
is-contr A = Σ A (λ a → (x : A) → Id a x)

abstract
  center :
    {l : Level} {A : UU l} → is-contr A → A
  center (pair c is-contr-A) = c
  
-- We make sure that the contraction is coherent in a straightforward way
eq-is-contr' :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → Id x y
eq-is-contr' (pair c C) x y = (inv (C x)) ∙ (C y)

eq-is-contr :
  {l : Level} {A : UU l} → is-contr A → {x y : A} → Id x y
eq-is-contr C {x} {y} = eq-is-contr' C x y

abstract
  contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    (const A A (center is-contr-A) ~ id)
  contraction C x = eq-is-contr C
  
  coh-contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    Id (contraction is-contr-A (center is-contr-A)) refl
  coh-contraction (pair c C) = left-inv (C c)

{- Remark 10.1.2 -}

{- Remark 10.1.3 -}

{- Theorem 10.1.4 -}

--------------------------------------------------------------------------------

-- Section 10.2 Singleton induction

-- We show that contractible types satisfy an induction principle akin to the induction principle of the unit type: singleton induction. This can be helpful to give short proofs of many facts.

{- Definition 10.2.1 -}

ev-pt :
  {l1 l2 : Level} {A : UU l1} (a : A) (B : A → UU l2) → ((x : A) → B x) → B a
ev-pt a B f = f a

is-singleton :
  (l : Level) {i : Level} (A : UU i) → A → UU (lsuc l ⊔ i)
is-singleton l A a = (B : A → UU l) → sec (ev-pt a B)

ind-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) →
  ({l : Level} → is-singleton l A a) → (B : A → UU l2) →
  B a → (x : A) → B x
ind-is-singleton a is-sing-A B = pr1 (is-sing-A B)

comp-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) (H : {l : Level} → is-singleton l A a) →
  (B : A → UU l2) → (ev-pt a B ∘ ind-is-singleton a H B) ~ id
comp-is-singleton a H B = pr2 (H B)

{- Theorem 10.2.3 -}

abstract
  ind-singleton-is-contr :
    {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
    B a → (x : A) → B x
  ind-singleton-is-contr a is-contr-A B b x =
    tr B ((inv (contraction is-contr-A a)) ∙ (contraction is-contr-A x)) b
  
  comp-singleton-is-contr :
    {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
    ((ev-pt a B) ∘ (ind-singleton-is-contr a is-contr-A B)) ~ id
  comp-singleton-is-contr a is-contr-A B b =
    ap (λ ω → tr B ω b) (left-inv (contraction is-contr-A a))

is-singleton-is-contr :
  {l1 l2 : Level} {A : UU l1} (a : A) → is-contr A → is-singleton l2 A a
pr1 (is-singleton-is-contr a is-contr-A B) =
  ind-singleton-is-contr a is-contr-A B
pr2 (is-singleton-is-contr a is-contr-A B) =
  comp-singleton-is-contr a is-contr-A B

abstract
  is-contr-ind-singleton :
    {i : Level} (A : UU i) (a : A) →
    ({l : Level} (P : A → UU l) → P a → (x : A) → P x) → is-contr A
  pr1 (is-contr-ind-singleton A a S) = a
  pr2 (is-contr-ind-singleton A a S) = S (λ x → Id a x) refl

abstract
  is-contr-is-singleton :
    {i : Level} (A : UU i) (a : A) →
    ({l : Level} → is-singleton l A a) → is-contr A
  is-contr-is-singleton A a S = is-contr-ind-singleton A a (λ P → pr1 (S P))

abstract
  is-singleton-unit : {l : Level} → is-singleton l unit star
  pr1 (is-singleton-unit B) = ind-unit
  pr2 (is-singleton-unit B) = refl-htpy

is-contr-unit : is-contr unit
is-contr-unit = is-contr-is-singleton unit star (is-singleton-unit)

abstract
  is-singleton-total-path :
    {i l : Level} (A : UU i) (a : A) →
    is-singleton l (Σ A (λ x → Id a x)) (pair a refl)
  pr1 (is-singleton-total-path A a B) = ind-Σ ∘ (ind-Id a _)
  pr2 (is-singleton-total-path A a B) = refl-htpy

abstract
  is-contr-total-path :
    {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id a x))
  is-contr-total-path {A = A} a =
    is-contr-is-singleton _ _ (is-singleton-total-path A a)

--------------------------------------------------------------------------------

-- Section 10.3 Contractible maps

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where
  
  {- Definition 10.3.1 -}
  
  fib : UU (l1 ⊔ l2)
  fib = Σ A (λ x → Id (f x) b)

  fib' : UU (l1 ⊔ l2)
  fib' = Σ A (λ x → Id b (f x))

  {- Definition 10.3.2 -}
  
  Eq-fib : fib → fib → UU (l1 ⊔ l2)
  Eq-fib s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id ((ap f α) ∙ (pr2 t)) (pr2 s))

  {- Proposition 10.3.3 -}
  
  refl-Eq-fib : (s : fib) → Eq-fib s s
  pr1 (refl-Eq-fib s) = refl
  pr2 (refl-Eq-fib s) = refl

  Eq-eq-fib : {s t : fib} → Id s t → Eq-fib s t
  Eq-eq-fib {s} refl = refl-Eq-fib s

  eq-Eq-fib' : {s t : fib} → Eq-fib s t → Id s t
  eq-Eq-fib' {pair x p} {pair .x .p} (pair refl refl) = refl

  eq-Eq-fib :
    {s t : fib} (α : Id (pr1 s) (pr1 t)) →
    Id ((ap f α) ∙ (pr2 t)) (pr2 s) → Id s t
  eq-Eq-fib α β = eq-Eq-fib' (pair α β)

  issec-eq-Eq-fib : {s t : fib} → (Eq-eq-fib {s} {t} ∘ eq-Eq-fib' {s} {t}) ~ id
  issec-eq-Eq-fib {pair x p} {pair .x .p} (pair refl refl) = refl

  isretr-eq-Eq-fib : {s t : fib} → (eq-Eq-fib' {s} {t} ∘ Eq-eq-fib {s} {t}) ~ id
  isretr-eq-Eq-fib {pair x p} {.(pair x p)} refl = refl

  abstract
    is-equiv-Eq-eq-fib : {s t : fib} → is-equiv (Eq-eq-fib {s} {t})
    is-equiv-Eq-eq-fib {s} {t} =
      is-equiv-has-inverse
        eq-Eq-fib'
        issec-eq-Eq-fib
        isretr-eq-Eq-fib

  equiv-Eq-eq-fib : {s t : fib} → Id s t ≃ Eq-fib s t
  pr1 (equiv-Eq-eq-fib {s} {t}) = Eq-eq-fib
  pr2 (equiv-Eq-eq-fib {s} {t}) = is-equiv-Eq-eq-fib

  abstract
    is-equiv-eq-Eq-fib :
      {s t : fib} → is-equiv (eq-Eq-fib' {s} {t})
    is-equiv-eq-Eq-fib {s} {t} =
      is-equiv-has-inverse
        Eq-eq-fib
        isretr-eq-Eq-fib
        issec-eq-Eq-fib

  equiv-eq-Eq-fib : {s t : fib} → Eq-fib s t ≃ Id s t
  pr1 (equiv-eq-Eq-fib {s} {t}) = eq-Eq-fib'
  pr2 (equiv-eq-Eq-fib {s} {t}) = is-equiv-eq-Eq-fib

{- Definition 10.3.4 -}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-map : (A → B) → UU (l1 ⊔ l2)
  is-contr-map f = (y : B) → is-contr (fib f y)

{- Theorem 10.3.5 -}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where
  
  map-inv-is-contr-map : is-contr-map f → B → A
  map-inv-is-contr-map H y = pr1 (center (H y))

  issec-map-inv-is-contr-map :
    (H : is-contr-map f) → (f ∘ (map-inv-is-contr-map H)) ~ id
  issec-map-inv-is-contr-map H y = pr2 (center (H y))

  isretr-map-inv-is-contr-map :
    (H : is-contr-map f) → ((map-inv-is-contr-map H) ∘ f) ~ id
  isretr-map-inv-is-contr-map H x =
    ap ( pr1 {B = λ z → Id (f z) (f x)})
       ( ( inv
           ( contraction
             ( H (f x))
             ( pair
               ( map-inv-is-contr-map H (f x))
               ( issec-map-inv-is-contr-map H (f x))))) ∙
         ( contraction (H (f x)) (pair x refl)))

  abstract
    is-equiv-is-contr-map : is-contr-map f → is-equiv f
    is-equiv-is-contr-map H =
      is-equiv-has-inverse
        ( map-inv-is-contr-map H)
        ( issec-map-inv-is-contr-map H)
        ( isretr-map-inv-is-contr-map H)

--------------------------------------------------------------------------------

-- Section 10.4 Equivalences are contractible maps

{- Definition 10.4.1 -}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  coherence-is-coherently-invertible :
    (g : B → A) (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
  coherence-is-coherently-invertible g G H = (G ·r f) ~ (f ·l H)

  is-coherently-invertible : UU (l1 ⊔ l2)
  is-coherently-invertible =
    Σ ( B → A)
      ( λ g → Σ ((f ∘ g) ~ id)
        ( λ G → Σ ((g ∘ f) ~ id)
          (λ H → coherence-is-coherently-invertible g G H)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  inv-is-coherently-invertible : is-coherently-invertible f → B → A
  inv-is-coherently-invertible = pr1

  issec-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) → (f ∘ inv-is-coherently-invertible H) ~ id
  issec-inv-is-coherently-invertible H = pr1 (pr2 H)
  
  isretr-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) → (inv-is-coherently-invertible H ∘ f) ~ id
  isretr-inv-is-coherently-invertible H = pr1 (pr2 (pr2 H))

  coh-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) →
    coherence-is-coherently-invertible f
      ( inv-is-coherently-invertible H)
      ( issec-inv-is-coherently-invertible H)
      ( isretr-inv-is-coherently-invertible H)
  coh-inv-is-coherently-invertible H = pr2 (pr2 (pr2 H))

  {- Proposition 10.4.2 -}
  
  abstract
    center-fib-is-coherently-invertible :
      is-coherently-invertible f → (y : B) → fib f y
    pr1 (center-fib-is-coherently-invertible H y) =
      inv-is-coherently-invertible H y
    pr2 (center-fib-is-coherently-invertible H y) =
      issec-inv-is-coherently-invertible H y

    contraction-fib-is-coherently-invertible :
      (H : is-coherently-invertible f) → (y : B) → (t : fib f y) →
      Id (center-fib-is-coherently-invertible H y) t
    contraction-fib-is-coherently-invertible H y (pair x refl) =
      eq-Eq-fib f y
        ( isretr-inv-is-coherently-invertible H x)
        ( ( right-unit) ∙
          ( inv ( coh-inv-is-coherently-invertible H x)))

  is-contr-map-is-coherently-invertible : 
    is-coherently-invertible f → is-contr-map f
  pr1 (is-contr-map-is-coherently-invertible H y) =
    center-fib-is-coherently-invertible H y
  pr2 (is-contr-map-is-coherently-invertible H y) =
    contraction-fib-is-coherently-invertible H y
  
{- Definition 10.4.3 -}

htpy-nat :
  {i j : Level} {A : UU i} {B : UU j} {f g : A → B} (H : f ~ g)
  {x y : A} (p : Id x y) →
  Id ((H x) ∙ (ap g p)) ((ap f p) ∙ (H y))
htpy-nat H refl = right-unit

{- Definition 10.4.4 -}

left-unwhisk :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) {q r : Id y z} →
  Id (p ∙ q) (p ∙ r) → Id q r
left-unwhisk refl s = (inv left-unit) ∙ (s ∙ left-unit)

right-unwhisk :
  {i : Level} {A : UU i} {x y z : A} {p q : Id x y}
  (r : Id y z) → Id (p ∙ r) (q ∙ r) → Id p q
right-unwhisk refl s = (inv right-unit) ∙ (s ∙ right-unit)

htpy-red :
  {i : Level} {A : UU i} {f : A → A} (H : f ~ id) →
  (x : A) → Id (H (f x)) (ap f (H x))
htpy-red {_} {A} {f} H x =
  right-unwhisk (H x)
    ( ( ap (concat (H (f x)) x) (inv (ap-id (H x)))) ∙
      ( htpy-nat H (H x)))

{- Lemma 10.4.5 -}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : has-inverse f)
  where
  
  inv-has-inverse : B → A
  inv-has-inverse = pr1 H
  
  issec-inv-has-inverse : (f ∘ inv-has-inverse) ~ id
  issec-inv-has-inverse y =
    ( inv (pr1 (pr2 H) (f (inv-has-inverse y)))) ∙
    ( ap f (pr2 (pr2 H) (inv-has-inverse y)) ∙ (pr1 (pr2 H) y))
  
  isretr-inv-has-inverse : (inv-has-inverse ∘ f) ~ id
  isretr-inv-has-inverse = pr2 (pr2 H)
  
  coherence-inv-has-inverse :
    (issec-inv-has-inverse ·r f) ~ (f ·l isretr-inv-has-inverse)
  coherence-inv-has-inverse x =
    inv
      ( inv-con
        ( pr1 (pr2 H) (f (inv-has-inverse (f x))))
        ( ap f (pr2 (pr2 H) x))
        ( (ap f (pr2 (pr2 H) (inv-has-inverse (f x)))) ∙ (pr1 (pr2 H) (f x)))
        ( sq-top-whisk
          ( pr1 (pr2 H) (f (inv-has-inverse (f x))))
          ( ap f (pr2 (pr2 H) x))
          ( (ap (f ∘ (inv-has-inverse ∘ f)) (pr2 (pr2 H) x)))
          ( ( ap-comp f (inv-has-inverse ∘ f) (pr2 (pr2 H) x)) ∙
            ( inv (ap (ap f) (htpy-red (pr2 (pr2 H)) x))))
          ( pr1 (pr2 H) (f x))
          ( htpy-nat (htpy-right-whisk (pr1 (pr2 H)) f) (pr2 (pr2 H) x))))

  is-coherently-invertible-has-inverse : is-coherently-invertible f
  pr1 is-coherently-invertible-has-inverse = inv-has-inverse
  pr1 (pr2 is-coherently-invertible-has-inverse) = issec-inv-has-inverse
  pr1 (pr2 (pr2 is-coherently-invertible-has-inverse)) = isretr-inv-has-inverse
  pr2 (pr2 (pr2 is-coherently-invertible-has-inverse)) =
    coherence-inv-has-inverse
  
{- Theorem 10.4.6 -}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where
  
  abstract
    is-contr-map-is-equiv : is-equiv f → is-contr-map f
    is-contr-map-is-equiv = 
      is-contr-map-is-coherently-invertible ∘
        ( is-coherently-invertible-has-inverse ∘
          has-inverse-is-equiv)

{- Corollary 10.4.7 -}

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-contr-total-path' : (a : A) → is-contr (Σ A (λ x → Id x a))
    is-contr-total-path' a = is-contr-map-is-equiv is-equiv-id a

-- Bureaucracy

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  issec-map-inv-is-equiv : (f ∘ map-inv-is-equiv H) ~ id
  issec-map-inv-is-equiv = issec-inv-has-inverse (has-inverse-is-equiv H)

  isretr-map-inv-is-equiv : (map-inv-is-equiv H ∘ f) ~ id
  isretr-map-inv-is-equiv =
    isretr-inv-has-inverse (has-inverse-is-equiv H)
  
  coherence-map-inv-is-equiv :
    ( issec-map-inv-is-equiv ·r f) ~ (f ·l isretr-map-inv-is-equiv)
  coherence-map-inv-is-equiv =
    coherence-inv-has-inverse (has-inverse-is-equiv H)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-inv-equiv : B → A
  map-inv-equiv = map-inv-is-equiv (is-equiv-map-equiv e)

  issec-map-inv-equiv : ((map-equiv e) ∘ map-inv-equiv) ~ id
  issec-map-inv-equiv = issec-map-inv-is-equiv (is-equiv-map-equiv e)

  isretr-map-inv-equiv : (map-inv-equiv ∘ (map-equiv e)) ~ id
  isretr-map-inv-equiv =
    isretr-map-inv-is-equiv (is-equiv-map-equiv e)
  
  coherence-map-inv-equiv :
    ( issec-map-inv-equiv ·r (map-equiv e)) ~
    ( (map-equiv e) ·l isretr-map-inv-equiv)
  coherence-map-inv-equiv =
    coherence-map-inv-is-equiv (is-equiv-map-equiv e)

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 10.1

module _
  {l : Level} {A : UU l}
  where
  
  contraction-is-prop-is-contr :
    (H : is-contr A) {x y : A} (p : Id x y) → Id (eq-is-contr H) p
  contraction-is-prop-is-contr (pair c C) {x} refl = left-inv (C x)

  abstract
    is-prop-is-contr :
      is-contr A → (x y : A) → is-contr (Id x y)
    pr1 (is-prop-is-contr H x y) = eq-is-contr H
    pr2 (is-prop-is-contr H x y) = contraction-is-prop-is-contr H

-- Exercise 10.2

module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where

  abstract
    is-contr-retract-of : A retract-of B → is-contr B → is-contr A
    pr1 (is-contr-retract-of (pair i (pair r isretr)) H) = r (center H)
    pr2 (is-contr-retract-of (pair i (pair r isretr)) H) x =
      ap r (contraction H (i x)) ∙ (isretr x)

-- Exercise 10.3

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-equiv-terminal-map-is-contr :
      is-contr A → is-equiv (terminal-map {A = A})
    pr1 (pr1 (is-equiv-terminal-map-is-contr H)) = ind-unit (center H)
    pr2 (pr1 (is-equiv-terminal-map-is-contr H)) = ind-unit refl
    pr1 (pr2 (is-equiv-terminal-map-is-contr H)) = const unit A (center H)
    pr2 (pr2 (is-equiv-terminal-map-is-contr H)) = contraction H

  abstract
    is-contr-is-equiv-const : is-equiv (terminal-map {A = A}) → is-contr A
    pr1 (is-contr-is-equiv-const (pair (pair g issec) (pair h isretr))) = h star
    pr2 (is-contr-is-equiv-const (pair (pair g issec) (pair h isretr))) = isretr

module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where
  
  abstract
    is-contr-is-equiv :
      (f : A → B) → is-equiv f → is-contr B → is-contr A
    is-contr-is-equiv f is-equiv-f is-contr-B =
      is-contr-is-equiv-const
        ( is-equiv-comp'
          ( terminal-map)
          ( f)
          ( is-equiv-f)
          ( is-equiv-terminal-map-is-contr is-contr-B))

  abstract
    is-contr-equiv : (e : A ≃ B) → is-contr B → is-contr A
    is-contr-equiv (pair e is-equiv-e) is-contr-B =
      is-contr-is-equiv e is-equiv-e is-contr-B

module _
  {l1 l2 : Level} (A : UU l1) {B : UU l2}
  where

  abstract
    is-contr-is-equiv' :
      (f : A → B) → is-equiv f → is-contr A → is-contr B
    is-contr-is-equiv' f is-equiv-f is-contr-A =
      is-contr-is-equiv A
        ( map-inv-is-equiv is-equiv-f)
        ( is-equiv-map-inv-is-equiv is-equiv-f)
        ( is-contr-A)

  abstract
    is-contr-equiv' : (e : A ≃ B) → is-contr A → is-contr B
    is-contr-equiv' (pair e is-equiv-e) is-contr-A =
      is-contr-is-equiv' e is-equiv-e is-contr-A

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-is-contr :
      (f : A → B) → is-contr A → is-contr B → is-equiv f
    is-equiv-is-contr f is-contr-A is-contr-B =
      is-equiv-has-inverse
        ( const B A (center is-contr-A))
        ( ind-singleton-is-contr _ is-contr-B _
          ( inv (contraction is-contr-B (f (center is-contr-A)))))
        ( contraction is-contr-A)

  equiv-is-contr : is-contr A → is-contr B → A ≃ B
  pr1 (equiv-is-contr is-contr-A is-contr-B) a = center is-contr-B
  pr2 (equiv-is-contr is-contr-A is-contr-B) =
    is-equiv-is-contr _ is-contr-A is-contr-B

map-equiv-Fin-one-ℕ : Fin one-ℕ → unit
map-equiv-Fin-one-ℕ (inr star) = star

inv-map-equiv-Fin-one-ℕ : unit → Fin one-ℕ
inv-map-equiv-Fin-one-ℕ star = inr star

issec-inv-map-equiv-Fin-one-ℕ :
  ( map-equiv-Fin-one-ℕ ∘ inv-map-equiv-Fin-one-ℕ) ~ id
issec-inv-map-equiv-Fin-one-ℕ star = refl

isretr-inv-map-equiv-Fin-one-ℕ :
  ( inv-map-equiv-Fin-one-ℕ ∘ map-equiv-Fin-one-ℕ) ~ id
isretr-inv-map-equiv-Fin-one-ℕ (inr star) = refl

is-equiv-map-equiv-Fin-one-ℕ : is-equiv map-equiv-Fin-one-ℕ
is-equiv-map-equiv-Fin-one-ℕ =
  is-equiv-has-inverse
    inv-map-equiv-Fin-one-ℕ
    issec-inv-map-equiv-Fin-one-ℕ
    isretr-inv-map-equiv-Fin-one-ℕ

equiv-Fin-one-ℕ : Fin one-ℕ ≃ unit
pr1 equiv-Fin-one-ℕ = map-equiv-Fin-one-ℕ
pr2 equiv-Fin-one-ℕ = is-equiv-map-equiv-Fin-one-ℕ

is-contr-Fin-one-ℕ : is-contr (Fin one-ℕ)
is-contr-Fin-one-ℕ = is-contr-equiv unit equiv-Fin-one-ℕ is-contr-unit

-- Exercise 10.4

is-not-contractible : {l : Level} → UU l → UU l
is-not-contractible X = ¬ (is-contr X)

is-not-contractible-is-empty :
  {l : Level} {X : UU l} → is-empty X → is-not-contractible X
is-not-contractible-is-empty H C = H (center C)

is-not-contractible-empty : is-not-contractible empty
is-not-contractible-empty = is-not-contractible-is-empty id

is-not-contractible-Fin :
  (k : ℕ) → is-not-one-ℕ k → is-not-contractible (Fin k)
is-not-contractible-Fin zero-ℕ f = is-not-contractible-empty
is-not-contractible-Fin (succ-ℕ zero-ℕ) f C = f refl
is-not-contractible-Fin (succ-ℕ (succ-ℕ k)) f C =
  Eq-Fin-eq (eq-is-contr' C neg-two-Fin neg-one-Fin)

-- Exercise 10.5

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    is-contr-left-factor-prod : is-contr (A × B) → is-contr A
    is-contr-left-factor-prod is-contr-AB =
      is-contr-retract-of
        ( A × B)
        ( pair
          ( λ x → pair x (pr2 (center is-contr-AB)))
          ( pair pr1 (λ x → refl)))
        ( is-contr-AB)

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    is-contr-right-factor-prod : is-contr (A × B) → is-contr B
    is-contr-right-factor-prod is-contr-AB =
      is-contr-left-factor-prod B A
        ( is-contr-equiv
          ( A × B)
          ( equiv-swap-prod B A)
          ( is-contr-AB))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  abstract
    is-contr-prod : is-contr A → is-contr B → is-contr (A × B)
    pr1 (pr1 (is-contr-prod (pair a C) (pair b D))) = a
    pr2 (pr1 (is-contr-prod (pair a C) (pair b D))) = b
    pr2 (is-contr-prod (pair a C) (pair b D)) (pair x y) = eq-pair (C x) (D y)

-- Exercise 10.6

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A)
  where

  map-inv-left-unit-law-Σ-is-contr : B a → Σ A B
  pr1 (map-inv-left-unit-law-Σ-is-contr b) = a
  pr2 (map-inv-left-unit-law-Σ-is-contr b) = b

  map-left-unit-law-Σ-is-contr : Σ A B → B a
  map-left-unit-law-Σ-is-contr =
    ind-Σ
      ( ind-singleton-is-contr a C
        ( λ x → B x → B a)
        ( id))

  issec-map-inv-left-unit-law-Σ-is-contr :
    ( map-left-unit-law-Σ-is-contr ∘ map-inv-left-unit-law-Σ-is-contr) ~ id
  issec-map-inv-left-unit-law-Σ-is-contr b =
    ap ( λ (f : B a → B a) → f b)
       ( comp-singleton-is-contr a C (λ x → B x → B a) id)
  
  isretr-map-inv-left-unit-law-Σ-is-contr :
    ( map-inv-left-unit-law-Σ-is-contr ∘ map-left-unit-law-Σ-is-contr) ~ id
  isretr-map-inv-left-unit-law-Σ-is-contr = 
    ind-Σ
      ( ind-singleton-is-contr a C
        ( λ x →
          ( y : B x) →
            Id ( ( map-inv-left-unit-law-Σ-is-contr ∘
                   map-left-unit-law-Σ-is-contr)
                 ( pair x y))
               ( pair x y))
        ( λ y → ap
          ( map-inv-left-unit-law-Σ-is-contr)
          ( ap ( λ f → f y)
               ( comp-singleton-is-contr a C (λ x → B x → B a) id))))

  abstract
    is-equiv-map-left-unit-law-Σ-is-contr :
      is-equiv map-left-unit-law-Σ-is-contr
    is-equiv-map-left-unit-law-Σ-is-contr =
      is-equiv-has-inverse
        map-inv-left-unit-law-Σ-is-contr
        issec-map-inv-left-unit-law-Σ-is-contr
        isretr-map-inv-left-unit-law-Σ-is-contr

  left-unit-law-Σ-is-contr : Σ A B ≃ B a
  pr1 left-unit-law-Σ-is-contr = map-left-unit-law-Σ-is-contr
  pr2 left-unit-law-Σ-is-contr = is-equiv-map-left-unit-law-Σ-is-contr

  abstract
    is-equiv-map-inv-left-unit-law-Σ-is-contr :
      is-equiv map-inv-left-unit-law-Σ-is-contr
    is-equiv-map-inv-left-unit-law-Σ-is-contr =
      is-equiv-has-inverse
        map-left-unit-law-Σ-is-contr
        isretr-map-inv-left-unit-law-Σ-is-contr
        issec-map-inv-left-unit-law-Σ-is-contr
  
  inv-left-unit-law-Σ-is-contr : B a ≃ Σ A B
  pr1 inv-left-unit-law-Σ-is-contr = map-inv-left-unit-law-Σ-is-contr
  pr2 inv-left-unit-law-Σ-is-contr = is-equiv-map-inv-left-unit-law-Σ-is-contr

  abstract
    is-contr-Σ :
      is-contr (B a) → is-contr (Σ A B)
    is-contr-Σ is-contr-B =
      is-contr-equiv
        ( B a)
        ( left-unit-law-Σ-is-contr)
        ( is-contr-B)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-contr-Σ' :
      is-contr A → ((x : A) → is-contr (B x)) → is-contr (Σ A B)
    is-contr-Σ' is-contr-A is-contr-B =
      is-contr-equiv
        ( B (center is-contr-A))
        ( left-unit-law-Σ-is-contr is-contr-A (center is-contr-A))
        ( is-contr-B (center is-contr-A))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (C : is-contr A)
  where
  
  left-unit-law-prod-is-contr : (A × B) ≃ B
  left-unit-law-prod-is-contr =
    left-unit-law-Σ-is-contr C (center C)

-- Exercise 10.7

-- Exercise 10.7 (a)

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where

  map-fib-pr1 : fib (pr1 {B = B}) a → B a
  map-fib-pr1 (pair (pair x y) p) = tr B p y

  map-inv-fib-pr1 : B a → fib (pr1 {B = B}) a
  map-inv-fib-pr1 b = pair (pair a b) refl

  issec-map-inv-fib-pr1 : (map-inv-fib-pr1 ∘ map-fib-pr1) ~ id
  issec-map-inv-fib-pr1 (pair (pair .a y) refl) = refl

  isretr-map-inv-fib-pr1 : (map-fib-pr1 ∘ map-inv-fib-pr1) ~ id
  isretr-map-inv-fib-pr1 b = refl

  abstract
    is-equiv-map-fib-pr1 : is-equiv map-fib-pr1
    is-equiv-map-fib-pr1 =
      is-equiv-has-inverse
        map-inv-fib-pr1
        isretr-map-inv-fib-pr1
        issec-map-inv-fib-pr1

  equiv-fib-pr1 : fib (pr1 {B = B}) a ≃ B a
  pr1 equiv-fib-pr1 = map-fib-pr1
  pr2 equiv-fib-pr1 = is-equiv-map-fib-pr1

  abstract
    is-equiv-map-inv-fib-pr1 : is-equiv map-inv-fib-pr1
    is-equiv-map-inv-fib-pr1 =
      is-equiv-has-inverse
        map-fib-pr1
        issec-map-inv-fib-pr1
        isretr-map-inv-fib-pr1

  inv-equiv-fib-pr1 : B a ≃ fib (pr1 {B = B}) a
  pr1 inv-equiv-fib-pr1 = map-inv-fib-pr1
  pr2 inv-equiv-fib-pr1 = is-equiv-map-inv-fib-pr1

-- Exercise 10.7 (b)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-equiv-pr1-is-contr : ((a : A) → is-contr (B a)) → is-equiv (pr1 {B = B})
    is-equiv-pr1-is-contr is-contr-B =
      is-equiv-is-contr-map
        ( λ x → is-contr-equiv
          ( B x)
          ( equiv-fib-pr1 B x)
          ( is-contr-B x))

  equiv-pr1 : ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
  pr1 (equiv-pr1 is-contr-B) = pr1
  pr2 (equiv-pr1 is-contr-B) = is-equiv-pr1-is-contr is-contr-B

  right-unit-law-Σ-is-contr : ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
  right-unit-law-Σ-is-contr = equiv-pr1

  abstract
    is-contr-is-equiv-pr1 : is-equiv (pr1 {B = B}) → ((a : A) → is-contr (B a))
    is-contr-is-equiv-pr1 is-equiv-pr1-B a =
      is-contr-equiv'
        ( fib pr1 a)
        ( equiv-fib-pr1 B a)
        ( is-contr-map-is-equiv is-equiv-pr1-B a)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  right-unit-law-prod-is-contr : is-contr B → (A × B) ≃ A
  right-unit-law-prod-is-contr H = right-unit-law-Σ-is-contr (λ a → H)

-- Exercise 10.7 (c)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  map-section : ((x : A) → B x) → (A → Σ A B)
  pr1 (map-section b a) = a
  pr2 (map-section b a) = b a

  htpy-map-section :
    (b : (x : A) → B x) → (pr1 ∘ map-section b) ~ id
  htpy-map-section b a = refl

  is-equiv-map-section :
    (b : (x : A) → B x) → ((x : A) → is-contr (B x)) → is-equiv (map-section b)
  is-equiv-map-section b C =
    is-equiv-right-factor
      ( id)
      ( pr1)
      ( map-section b)
      ( htpy-map-section b)
      ( is-equiv-pr1-is-contr C)
      ( is-equiv-id)

  equiv-section :
    (b : (x : A) → B x) → ((x : A) → is-contr (B x)) → A ≃ Σ A B
  equiv-section b C = pair (map-section b) (is-equiv-map-section b C)

  is-contr-fam-is-equiv-map-section :
    (b : (x : A) → B x) → is-equiv (map-section b) → ((x : A) → is-contr (B x))
  is-contr-fam-is-equiv-map-section b H =
    is-contr-is-equiv-pr1
      ( is-equiv-left-factor id pr1
        ( map-section b)
        ( htpy-map-section b)
        ( is-equiv-id)
        ( H))

-- Exercise 10.8

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  map-equiv-total-fib : (Σ B (fib f)) → A
  map-equiv-total-fib t = pr1 (pr2 t)

  triangle-map-equiv-total-fib : pr1 ~ (f ∘ map-equiv-total-fib)
  triangle-map-equiv-total-fib t = inv (pr2 (pr2 t))

  map-inv-equiv-total-fib : A → Σ B (fib f)
  map-inv-equiv-total-fib x = pair (f x) (pair x refl)

  isretr-map-inv-equiv-total-fib :
    (map-inv-equiv-total-fib ∘ map-equiv-total-fib) ~ id
  isretr-map-inv-equiv-total-fib (pair .(f x) (pair x refl)) = refl

  issec-map-inv-equiv-total-fib :
    (map-equiv-total-fib ∘ map-inv-equiv-total-fib) ~ id
  issec-map-inv-equiv-total-fib x = refl

  abstract
    is-equiv-map-equiv-total-fib : is-equiv map-equiv-total-fib
    is-equiv-map-equiv-total-fib =
      is-equiv-has-inverse
        map-inv-equiv-total-fib
        issec-map-inv-equiv-total-fib
        isretr-map-inv-equiv-total-fib

    is-equiv-map-inv-equiv-total-fib : is-equiv map-inv-equiv-total-fib
    is-equiv-map-inv-equiv-total-fib =
      is-equiv-has-inverse
        map-equiv-total-fib
        isretr-map-inv-equiv-total-fib
        issec-map-inv-equiv-total-fib

  equiv-total-fib : Σ B (fib f) ≃ A
  pr1 equiv-total-fib = map-equiv-total-fib
  pr2 equiv-total-fib = is-equiv-map-equiv-total-fib

  inv-equiv-total-fib : A ≃ Σ B (fib f)
  pr1 inv-equiv-total-fib = map-inv-equiv-total-fib
  pr2 inv-equiv-total-fib = is-equiv-map-inv-equiv-total-fib
```
