---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.23-pullbacks where

open import univalent-foundations public

-- Section 13.1 Cartesian squares

-- Section 13.2

-- Section 13.3 Fiber products

-- Section 13.4 Fibers as pullbacks

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  square-fiber :
    ( f ∘ (pr1 {B = λ x → Id (f x) b})) ~
    ( (const unit B b) ∘ (const (fib f b) unit star))
  square-fiber = pr2

  cone-fiber : cone f (const unit B b) (fib f b)
  pr1 cone-fiber = pr1
  pr1 (pr2 cone-fiber) = const (fib f b) unit star
  pr2 (pr2 cone-fiber) = square-fiber

  abstract
    is-pullback-cone-fiber : is-pullback f (const unit B b) cone-fiber
    is-pullback-cone-fiber =
      is-equiv-tot-is-fiberwise-equiv
        (λ a → is-equiv-map-inv-left-unit-law-prod)

  abstract
    universal-property-pullback-cone-fiber :
      {l : Level} → universal-property-pullback l f (const unit B b) cone-fiber
    universal-property-pullback-cone-fiber =
      universal-property-pullback-is-pullback f
        ( const unit B b)
        ( cone-fiber)
        ( is-pullback-cone-fiber)

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where
  
  cone-fiber-fam : cone (pr1 {B = B}) (const unit A a) (B a)
  pr1 (pr1 cone-fiber-fam b) = a
  pr2 (pr1 cone-fiber-fam b) = b
  pr1 (pr2 cone-fiber-fam) = const (B a) unit star
  pr2 (pr2 cone-fiber-fam) = refl-htpy

  abstract
    is-pullback-cone-fiber-fam :
      is-pullback (pr1 {B = B}) (const unit A a) cone-fiber-fam
    is-pullback-cone-fiber-fam =
      is-equiv-comp
        ( gap (pr1 {B = B}) (const unit A a) cone-fiber-fam)
        ( gap (pr1 {B = B}) (const unit A a) (cone-fiber (pr1 {B = B}) a))
        ( map-inv-fib-pr1 B a)
        ( refl-htpy)
        ( is-equiv-map-inv-fib-pr1 B a)
        ( is-pullback-cone-fiber pr1 a)

-- Section 13.5 Fiberwise equivalences

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3)
  where
  
  cone-subst :
    cone f (pr1 {B = Q}) (Σ A (λ x → Q (f x)))
  pr1 cone-subst = pr1
  pr1 (pr2 cone-subst) = map-Σ-map-base f Q
  pr2 (pr2 cone-subst) = refl-htpy

  inv-gap-cone-subst :
    canonical-pullback f (pr1 {B = Q}) → Σ A (λ x → Q (f x))
  pr1 (inv-gap-cone-subst (pair x (pair (pair .(f x) q) refl))) = x
  pr2 (inv-gap-cone-subst (pair x (pair (pair .(f x) q) refl))) = q
  
  abstract
    issec-inv-gap-cone-subst :
      ((gap f (pr1 {B = Q}) cone-subst) ∘ inv-gap-cone-subst) ~ id
    issec-inv-gap-cone-subst (pair x (pair (pair .(f x) q) refl)) = refl

  abstract
    isretr-inv-gap-cone-subst :
      (inv-gap-cone-subst ∘ (gap f (pr1 {B = Q}) cone-subst)) ~ id
    isretr-inv-gap-cone-subst (pair x q) = refl

  abstract
    is-pullback-cone-subst : is-pullback f (pr1 {B = Q}) cone-subst
    is-pullback-cone-subst =
      is-equiv-has-inverse
        inv-gap-cone-subst
        issec-inv-gap-cone-subst
        isretr-inv-gap-cone-subst

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
  (Q : B → UU l4) (f : A → B) (g : (x : A) → (P x) → (Q (f x)))
  where
  
  cone-map-Σ : cone f (pr1 {B = Q}) (Σ A P)
  pr1 cone-map-Σ = pr1
  pr1 (pr2 cone-map-Σ) = map-Σ Q f g
  pr2 (pr2 cone-map-Σ) = refl-htpy

  abstract
    is-pullback-is-fiberwise-equiv :
      is-fiberwise-equiv g → is-pullback f (pr1 {B = Q}) cone-map-Σ
    is-pullback-is-fiberwise-equiv is-equiv-g =
      is-equiv-comp
        ( gap f pr1 cone-map-Σ)
        ( gap f pr1 (cone-subst f Q))
        ( tot g)
        ( refl-htpy)
        ( is-equiv-tot-is-fiberwise-equiv is-equiv-g)
        ( is-pullback-cone-subst f Q)

  abstract
    universal-property-pullback-is-fiberwise-equiv :
      is-fiberwise-equiv g → {l : Level} →
      universal-property-pullback l f (pr1 {B = Q}) cone-map-Σ
    universal-property-pullback-is-fiberwise-equiv is-equiv-g =
      universal-property-pullback-is-pullback f pr1 cone-map-Σ
        ( is-pullback-is-fiberwise-equiv is-equiv-g)

  abstract
    is-fiberwise-equiv-is-pullback :
      is-pullback f (pr1 {B = Q}) cone-map-Σ → is-fiberwise-equiv g
    is-fiberwise-equiv-is-pullback is-pullback-cone-map-Σ =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-right-factor
          ( gap f pr1 cone-map-Σ)
          ( gap f pr1 (cone-subst f Q))
          ( tot g)
          ( refl-htpy)
          ( is-pullback-cone-subst f Q)
          ( is-pullback-cone-map-Σ))

  abstract
    is-fiberwise-equiv-universal-property-pullback :
      ( {l : Level} →
        universal-property-pullback l f (pr1 {B = Q}) cone-map-Σ) →
      is-fiberwise-equiv g
    is-fiberwise-equiv-universal-property-pullback up =
      is-fiberwise-equiv-is-pullback
        ( is-pullback-universal-property-pullback f pr1 cone-map-Σ up)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where
  
  fib-square : (x : A) → fib (pr1 c) x → fib g (f x)
  pr1 (fib-square x t) = pr1 (pr2 c) (pr1 t)
  pr2 (fib-square x t) = (inv (pr2 (pr2 c) (pr1 t))) ∙ (ap f (pr2 t))

{-
fib-square-id :
  {l1 l2 : Level} {B : UU l1} {X : UU l2} (g : B → X) (x : X) →
  fib-square id g (triple g id refl-htpy) x ~ id
fib-square-id g .(g b) (pair b refl) =
  refl
-}

  square-tot-fib-square :
    ( (gap f g c) ∘ (map-equiv-total-fib (pr1 c))) ~
    ( (tot (λ a → tot (λ b → inv))) ∘ (tot fib-square))
  square-tot-fib-square (pair .((pr1 c) x) (pair x refl)) =
    eq-pair-Σ refl
      ( eq-pair-Σ refl
        ( inv ((ap inv right-unit) ∙ (inv-inv (pr2 (pr2 c) x)))))

  abstract
    is-fiberwise-equiv-fib-square-is-pullback :
      is-pullback f g c → is-fiberwise-equiv fib-square
    is-fiberwise-equiv-fib-square-is-pullback pb =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-is-equiv-bottom-square
          ( map-equiv-total-fib (pr1 c))
          ( tot (λ x → tot (λ y → inv)))
          ( tot fib-square)
          ( gap f g c)
          ( square-tot-fib-square)
          ( is-equiv-map-equiv-total-fib (pr1 c))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ x → is-equiv-tot-is-fiberwise-equiv
              ( λ y → is-equiv-inv (g y) (f x))))
          ( pb))

  abstract
    is-pullback-is-fiberwise-equiv-fib-square :
      is-fiberwise-equiv fib-square → is-pullback f g c
    is-pullback-is-fiberwise-equiv-fib-square is-equiv-fsq =
      is-equiv-bottom-is-equiv-top-square
        ( map-equiv-total-fib (pr1 c))
        ( tot (λ x → tot (λ y → inv)))
        ( tot fib-square)
        ( gap f g c)
        ( square-tot-fib-square)
        ( is-equiv-map-equiv-total-fib (pr1 c))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ x → is-equiv-tot-is-fiberwise-equiv
            ( λ y → is-equiv-inv (g y) (f x))))
        ( is-equiv-tot-is-fiberwise-equiv is-equiv-fsq)

module _
  {l1 l2 l3 l4 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where
  
  abstract
    is-trunc-is-pullback :
      is-pullback f g c → is-trunc-map k g → is-trunc-map k (pr1 c)
    is-trunc-is-pullback pb is-trunc-g a =
      is-trunc-is-equiv k
        ( fib g (f a))
        ( fib-square f g c a)
        ( is-fiberwise-equiv-fib-square-is-pullback f g c pb a)
        (is-trunc-g (f a))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where
  
  abstract
    is-emb-is-pullback : is-pullback f g c → is-emb g → is-emb (pr1 c)
    is-emb-is-pullback pb is-emb-g =
      is-emb-is-prop-map
        ( is-trunc-is-pullback neg-one-𝕋 f g c pb (is-prop-map-is-emb is-emb-g))

  abstract
    is-equiv-is-pullback : is-equiv g → is-pullback f g c → is-equiv (pr1 c)
    is-equiv-is-pullback is-equiv-g pb =
      is-equiv-is-contr-map
        ( is-trunc-is-pullback neg-two-𝕋 f g c pb
          ( is-contr-map-is-equiv is-equiv-g))

  abstract
    is-pullback-is-equiv : is-equiv g → is-equiv (pr1 c) → is-pullback f g c
    is-pullback-is-equiv is-equiv-g is-equiv-p =
      is-pullback-is-fiberwise-equiv-fib-square f g c
        ( λ a → is-equiv-is-contr
          ( fib-square f g c a)
          ( is-contr-map-is-equiv is-equiv-p a)
          ( is-contr-map-is-equiv is-equiv-g (f a)))

-- Section 13.6 The pullback pasting property

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where
  
  cone-comp-horizontal :
    (c : cone j h B) → (cone i (pr1 c) A) → cone (j ∘ i) h A
  pr1 (cone-comp-horizontal (pair g (pair q K)) (pair f (pair p H))) = f
  pr1
    ( pr2
      ( cone-comp-horizontal (pair g (pair q K)) (pair f (pair p H)))) = q ∘ p
  pr2
    ( pr2
      ( cone-comp-horizontal (pair g (pair q K)) (pair f (pair p H)))) =
    coherence-square-comp-horizontal p q f g h i j H K

  fib-square-comp-horizontal :
    (c : cone j h B) (d : cone i (pr1 c) A) → (x : X) →
    ( fib-square (j ∘ i) h (cone-comp-horizontal c d) x) ~
    ( (fib-square j h c (i x)) ∘ (fib-square i (pr1 c) d x))
  fib-square-comp-horizontal
    (pair g (pair q K)) (pair f (pair p H)) .(f a) (pair a refl) =
    eq-pair-Σ
      ( refl)
      ( ( ap
          ( concat' (h (q (p a))) refl)
          ( distributive-inv-concat (ap j (H a)) (K (p a)))) ∙
        ( ( assoc (inv (K (p a))) (inv (ap j (H a))) refl) ∙
          ( ap
            ( concat (inv (K (p a))) (j (i (f a))))
            ( ( ap (concat' (j (g (p a))) refl) (inv (ap-inv j (H a)))) ∙
              ( inv (ap-concat j (inv (H a)) refl))))))

  abstract
    is-pullback-rectangle-is-pullback-left-square :
      (c : cone j h B) (d : cone i (pr1 c) A) →
      is-pullback j h c → is-pullback i (pr1 c) d →
      is-pullback (j ∘ i) h (cone-comp-horizontal c d)
    is-pullback-rectangle-is-pullback-left-square c d is-pb-c is-pb-d =
      is-pullback-is-fiberwise-equiv-fib-square (j ∘ i) h
        ( cone-comp-horizontal c d)
        ( λ x → is-equiv-comp
          ( fib-square (j ∘ i) h (cone-comp-horizontal c d) x)
          ( fib-square j h c (i x))
          ( fib-square i (pr1 c) d x)
          ( fib-square-comp-horizontal c d x)
          ( is-fiberwise-equiv-fib-square-is-pullback i (pr1 c) d is-pb-d x)
          ( is-fiberwise-equiv-fib-square-is-pullback j h c is-pb-c (i x)))

  abstract
    is-pullback-left-square-is-pullback-rectangle :
      (c : cone j h B) (d : cone i (pr1 c) A) →
      is-pullback j h c → is-pullback (j ∘ i) h (cone-comp-horizontal c d) →
      is-pullback i (pr1 c) d
    is-pullback-left-square-is-pullback-rectangle c d is-pb-c is-pb-rect =
      is-pullback-is-fiberwise-equiv-fib-square i (pr1 c) d
        ( λ x → is-equiv-right-factor
          ( fib-square (j ∘ i) h (cone-comp-horizontal c d) x)
          ( fib-square j h c (i x))
          ( fib-square i (pr1 c) d x)
          ( fib-square-comp-horizontal c d x)
          ( is-fiberwise-equiv-fib-square-is-pullback j h c is-pb-c (i x))
          ( is-fiberwise-equiv-fib-square-is-pullback (j ∘ i) h
            ( cone-comp-horizontal c d) is-pb-rect x))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where
  
  cone-comp-vertical :
    (c : cone f g B) → cone (pr1 (pr2 c)) h A → cone f (g ∘ h) A
  pr1 (cone-comp-vertical (pair p (pair q H)) (pair p' (pair q' H'))) = p ∘ p'
  pr1 (pr2 (cone-comp-vertical (pair p (pair q H)) (pair p' (pair q' H')))) = q'
  pr2 (pr2 (cone-comp-vertical (pair p (pair q H)) (pair p' (pair q' H')))) =
    coherence-square-comp-vertical q' p' h q p g f H' H

  fib-square-comp-vertical : 
    (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) (x : C) →
    ( ( fib-square f (g ∘ h) (cone-comp-vertical c d) x) ∘
      ( inv-map-fib-comp (pr1 c) (pr1 d) x)) ~
    ( ( inv-map-fib-comp g h (f x)) ∘
      ( map-Σ
        ( λ t → fib h (pr1 t))
        ( fib-square f g c x)
        ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t))))
  fib-square-comp-vertical
    (pair p (pair q H)) (pair p' (pair q' H')) .(p (p' a))
    (pair (pair .(p' a) refl) (pair a refl)) =
    eq-pair-Σ refl
      ( ( right-unit) ∙
        ( ( distributive-inv-concat (H (p' a)) (ap g (H' a))) ∙
          ( ( ap
              ( concat (inv (ap g (H' a))) (f (p (p' a))))
              ( inv right-unit)) ∙
            ( ap
              ( concat' (g (h (q' a)))
                ( pr2
                  ( fib-square f g
                    ( triple p q H)
                    ( p (p' a))
                    ( pair (p' a) refl))))
              ( ( inv (ap-inv g (H' a))) ∙
                ( ap (ap g) (inv right-unit)))))))

  abstract
    is-pullback-top-is-pullback-rectangle :
      (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) →
      is-pullback f g c →
      is-pullback f (g ∘ h) (cone-comp-vertical c d) →
      is-pullback (pr1 (pr2 c)) h d
    is-pullback-top-is-pullback-rectangle c d is-pb-c is-pb-dc =
      is-pullback-is-fiberwise-equiv-fib-square (pr1 (pr2 c)) h d
        ( λ x → is-fiberwise-equiv-is-equiv-map-Σ
          ( λ t → fib h (pr1 t))
          ( fib-square f g c ((pr1 c) x))
          ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t))
          ( is-fiberwise-equiv-fib-square-is-pullback f g c is-pb-c ((pr1 c) x))
          ( is-equiv-top-is-equiv-bottom-square
            ( inv-map-fib-comp (pr1 c) (pr1 d) ((pr1 c) x))
            ( inv-map-fib-comp g h (f ((pr1 c) x)))
            ( map-Σ
              ( λ t → fib h (pr1 t))
              ( fib-square f g c ((pr1 c) x))
              ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t)))
            ( fib-square f (g ∘ h) (cone-comp-vertical c d) ((pr1 c) x))
            ( fib-square-comp-vertical c d ((pr1 c) x))
            ( is-equiv-inv-map-fib-comp (pr1 c) (pr1 d) ((pr1 c) x))
            ( is-equiv-inv-map-fib-comp g h (f ((pr1 c) x)))
            ( is-fiberwise-equiv-fib-square-is-pullback f (g ∘ h)
              ( cone-comp-vertical c d) is-pb-dc ((pr1 c) x)))
          ( pair x refl))

  abstract
    is-pullback-rectangle-is-pullback-top :
      (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) →
      is-pullback f g c →
      is-pullback (pr1 (pr2 c)) h d →
      is-pullback f (g ∘ h) (cone-comp-vertical c d)
    is-pullback-rectangle-is-pullback-top c d is-pb-c is-pb-d =
      is-pullback-is-fiberwise-equiv-fib-square f (g ∘ h)
        ( cone-comp-vertical c d)
        ( λ x → is-equiv-bottom-is-equiv-top-square
          ( inv-map-fib-comp (pr1 c) (pr1 d) x)
          ( inv-map-fib-comp g h (f x))
          ( map-Σ
            ( λ t → fib h (pr1 t))
            ( fib-square f g c x)
            ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t)))
          ( fib-square f (g ∘ h) (cone-comp-vertical c d) x)
          ( fib-square-comp-vertical c d x)
          ( is-equiv-inv-map-fib-comp (pr1 c) (pr1 d) x)
          ( is-equiv-inv-map-fib-comp g h (f x))
          ( is-equiv-map-Σ
            ( λ t → fib h (pr1 t))
            ( fib-square f g c x)
            ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t))
            ( is-fiberwise-equiv-fib-square-is-pullback f g c is-pb-c x)
            ( λ t → is-fiberwise-equiv-fib-square-is-pullback
              (pr1 (pr2 c)) h d is-pb-d (pr1 t)))) 

-- Section 13.7 Descent for coproducts and Σ-types

module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B)
  where

  fib-map-coprod-inl-fib : (x : A) → fib f x → fib (map-coprod f g) (inl x)
  pr1 (fib-map-coprod-inl-fib x (pair a' p)) = inl a'
  pr2 (fib-map-coprod-inl-fib x (pair a' p)) = ap inl p

  fib-fib-map-coprod-inl : (x : A) → fib (map-coprod f g) (inl x) → fib f x
  fib-fib-map-coprod-inl x (pair (inl a') p) =
    pair a' (map-compute-eq-coprod-inl-inl (f a') x p)
  fib-fib-map-coprod-inl x (pair (inr b') p) =
    ex-falso (is-empty-eq-coprod-inr-inl (g b') x p)

  abstract
    issec-fib-fib-map-coprod-inl :
      (x : A) → (fib-map-coprod-inl-fib x ∘ fib-fib-map-coprod-inl x) ~ id
    issec-fib-fib-map-coprod-inl .(f a') (pair (inl a') refl) = refl
    issec-fib-fib-map-coprod-inl x (pair (inr b') p) =
      ex-falso (is-empty-eq-coprod-inr-inl (g b') x p)

  abstract
    isretr-fib-fib-map-coprod-inl :
      (x : A) → (fib-fib-map-coprod-inl x ∘ fib-map-coprod-inl-fib x) ~ id
    isretr-fib-fib-map-coprod-inl .(f a') (pair a' refl) = refl

  abstract
    is-equiv-fib-map-coprod-inl-fib :
      (x : A) → is-equiv (fib-map-coprod-inl-fib x)
    is-equiv-fib-map-coprod-inl-fib x =
      is-equiv-has-inverse
        ( fib-fib-map-coprod-inl x)
        ( issec-fib-fib-map-coprod-inl x)
        ( isretr-fib-fib-map-coprod-inl x)

  fib-map-coprod-inr-fib : (y : B) → fib g y → fib (map-coprod f g) (inr y)
  pr1 (fib-map-coprod-inr-fib y (pair b' p)) = inr b'
  pr2 (fib-map-coprod-inr-fib y (pair b' p)) = ap inr p
  
  fib-fib-map-coprod-inr : (y : B) → fib (map-coprod f g) (inr y) → fib g y
  fib-fib-map-coprod-inr y (pair (inl a') p) =
    ex-falso (is-empty-eq-coprod-inl-inr (f a') y p)
  pr1 (fib-fib-map-coprod-inr y (pair (inr b') p)) = b'
  pr2 (fib-fib-map-coprod-inr y (pair (inr b') p)) =
    map-compute-eq-coprod-inr-inr (g b') y p

  abstract
    issec-fib-fib-map-coprod-inr :
      (y : B) → (fib-map-coprod-inr-fib y ∘ fib-fib-map-coprod-inr y) ~ id
    issec-fib-fib-map-coprod-inr .(g b') (pair (inr b') refl) = refl
    issec-fib-fib-map-coprod-inr y (pair (inl a') p) =
      ex-falso (is-empty-eq-coprod-inl-inr (f a') y p)

  abstract
    isretr-fib-fib-map-coprod-inr :
      (y : B) → (fib-fib-map-coprod-inr y ∘ fib-map-coprod-inr-fib y) ~ id
    isretr-fib-fib-map-coprod-inr .(g b') (pair b' refl) = refl

  abstract
    is-equiv-fib-map-coprod-inr-fib :
      (y : B) → is-equiv (fib-map-coprod-inr-fib y)
    is-equiv-fib-map-coprod-inr-fib y =
      is-equiv-has-inverse
        ( fib-fib-map-coprod-inr y)
        ( issec-fib-fib-map-coprod-inr y)
        ( isretr-fib-fib-map-coprod-inr y)

module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A' → A) (g : B' → B) (h : X' → X)
  (αA : A → X) (αB : B → X) (αA' : A' → X') (αB' : B' → X')
  (HA : (αA ∘ f) ~ (h ∘ αA')) (HB : (αB ∘ g) ~ (h ∘ αB'))
  where
  
  triangle-descent-square-fib-map-coprod-inl-fib :
    (x : A) →
    (fib-square αA h (triple f αA' HA) x) ~
      ( ( fib-square (ind-coprod _ αA αB) h
          ( triple
            ( map-coprod f g)
            ( ind-coprod _ αA' αB')
            ( ind-coprod _ HA HB))
          ( inl x)) ∘
      ( fib-map-coprod-inl-fib f g x))
  triangle-descent-square-fib-map-coprod-inl-fib x (pair a' p) =
    eq-pair-Σ refl
      ( ap (concat (inv (HA a')) (αA x))
        ( ap-comp (ind-coprod _ αA αB) inl p))

  triangle-descent-square-fib-map-coprod-inr-fib :
    (y : B) →
    (fib-square αB h (triple g αB' HB) y) ~
      ( ( fib-square (ind-coprod _ αA αB) h
          ( triple
            ( map-coprod f g)
            ( ind-coprod _ αA' αB')
            ( ind-coprod _ HA HB))
          ( inr y)) ∘
      ( fib-map-coprod-inr-fib f g y))
  triangle-descent-square-fib-map-coprod-inr-fib y ( pair b' p) =
    eq-pair-Σ refl
      ( ap (concat (inv (HB b')) (αB y))
        ( ap-comp (ind-coprod _ αA αB) inr p))

module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (i : X' → X)
  where
  
  cone-descent-coprod :
    (cone-A' : cone f i A') (cone-B' : cone g i B') →
    cone (ind-coprod _ f g) i (coprod A' B')
  pr1 (cone-descent-coprod (pair h (pair f' H)) (pair k (pair g' K))) =
    map-coprod h k
  pr1
    ( pr2 (cone-descent-coprod (pair h (pair f' H)) (pair k (pair g' K))))
    ( inl a') = f' a'
  pr1
    ( pr2 (cone-descent-coprod (pair h (pair f' H)) (pair k (pair g' K))))
    ( inr b') = g' b'
  pr2
    ( pr2 (cone-descent-coprod (pair h (pair f' H)) (pair k (pair g' K))))
    ( inl a') = H a'
  pr2
    ( pr2 (cone-descent-coprod (pair h (pair f' H)) (pair k (pair g' K))))
    ( inr b') = K b'

  abstract
    descent-coprod :
      (cone-A' : cone f i A') (cone-B' : cone g i B') →
      is-pullback f i cone-A' →
      is-pullback g i cone-B' →
      is-pullback (ind-coprod _ f g) i (cone-descent-coprod cone-A' cone-B')
    descent-coprod (pair h (pair f' H)) (pair k (pair g' K))
      is-pb-cone-A' is-pb-cone-B' =
      is-pullback-is-fiberwise-equiv-fib-square
        ( ind-coprod _ f g)
        ( i)
        ( cone-descent-coprod (triple h f' H) (triple k g' K))
        ( α)
      where
      α : is-fiberwise-equiv
          ( fib-square (ind-coprod (λ _ → X) f g) i
          ( cone-descent-coprod (triple h f' H) (triple k g' K)))
      α (inl x) =
        is-equiv-left-factor
          ( fib-square f i (triple h f' H) x)
          ( fib-square (ind-coprod _ f g) i
            ( cone-descent-coprod (triple h f' H) (triple k g' K))
            ( inl x))
          ( fib-map-coprod-inl-fib h k x)
          ( triangle-descent-square-fib-map-coprod-inl-fib
            h k i f g f' g' H K x)
          ( is-fiberwise-equiv-fib-square-is-pullback f i
            ( triple h f' H) is-pb-cone-A' x)
          ( is-equiv-fib-map-coprod-inl-fib h k x)
      α (inr y) =
        is-equiv-left-factor
          ( fib-square g i (triple k g' K) y)
          ( fib-square
            ( ind-coprod _ f g) i
            ( cone-descent-coprod (triple h f' H) (triple k g' K))
            ( inr y))
            ( fib-map-coprod-inr-fib h k y)
            ( triangle-descent-square-fib-map-coprod-inr-fib
              h k i f g f' g' H K y)
            ( is-fiberwise-equiv-fib-square-is-pullback g i
              ( triple k g' K) is-pb-cone-B' y)
            ( is-equiv-fib-map-coprod-inr-fib h k y)

  abstract
    descent-coprod-inl :
      (cone-A' : cone f i A') (cone-B' : cone g i B') →
      is-pullback (ind-coprod _ f g) i (cone-descent-coprod cone-A' cone-B') →
      is-pullback f i cone-A'
    descent-coprod-inl (pair h (pair f' H)) (pair k (pair g' K)) is-pb-dsq =
        is-pullback-is-fiberwise-equiv-fib-square f i (triple h f' H)
          ( λ a → is-equiv-comp
            ( fib-square f i (triple h f' H) a)
            ( fib-square (ind-coprod _ f g) i
              ( cone-descent-coprod (triple h f' H) (triple k g' K))
              ( inl a))
            ( fib-map-coprod-inl-fib h k a)
            ( triangle-descent-square-fib-map-coprod-inl-fib
              h k i f g f' g' H K a)
            ( is-equiv-fib-map-coprod-inl-fib h k a)
            ( is-fiberwise-equiv-fib-square-is-pullback (ind-coprod _ f g) i
              ( cone-descent-coprod ( triple h f' H) (triple k g' K))
              ( is-pb-dsq)
              ( inl a)))

  abstract
    descent-coprod-inr :
      (cone-A' : cone f i A') (cone-B' : cone g i B') →
      is-pullback (ind-coprod _ f g) i (cone-descent-coprod cone-A' cone-B') →
      is-pullback g i cone-B'
    descent-coprod-inr (pair h (pair f' H)) (pair k (pair g' K)) is-pb-dsq =
        is-pullback-is-fiberwise-equiv-fib-square g i (triple k g' K)
          ( λ b → is-equiv-comp
            ( fib-square g i (triple k g' K) b)
            ( fib-square (ind-coprod _ f g) i
              ( cone-descent-coprod (triple h f' H) (triple k g' K))
              ( inr b))
            ( fib-map-coprod-inr-fib h k b)
            ( triangle-descent-square-fib-map-coprod-inr-fib
              h k i f g f' g' H K b)
            ( is-equiv-fib-map-coprod-inr-fib h k b)
            ( is-fiberwise-equiv-fib-square-is-pullback (ind-coprod _ f g) i
              ( cone-descent-coprod (triple h f' H) (triple k g' K))
              ( is-pb-dsq)
              ( inr b)))

-- Descent for Σ-types

module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
  (f : (i : I) → A i → X) (h : X' → X)
  (c : (i : I) → cone (f i) h (A' i))
  where

  cone-descent-Σ : cone (ind-Σ f) h (Σ I A')
  cone-descent-Σ =
    triple
      ( tot (λ i → (pr1 (c i))))
      ( ind-Σ (λ i → (pr1 (pr2 (c i)))))
      ( ind-Σ (λ i → (pr2 (pr2 (c i)))))

  triangle-descent-Σ :
    (i : I) (a : A i) →
    ( fib-square (f i) h (c i) a) ~
    ( ( fib-square (ind-Σ f) h cone-descent-Σ (pair i a)) ∘
      ( map-inv-compute-fib-tot (λ i → (pr1 (c i))) (pair i a)))
  triangle-descent-Σ i .(pr1 (c i) a') (pair a' refl) = refl

  abstract
    descent-Σ : 
      ((i : I) → is-pullback (f i) h (c i)) →
      is-pullback (ind-Σ f) h cone-descent-Σ
    descent-Σ is-pb-c =
      is-pullback-is-fiberwise-equiv-fib-square
        ( ind-Σ f)
        ( h)
        ( cone-descent-Σ)
        ( ind-Σ
          ( λ i a → is-equiv-left-factor
            ( fib-square (f i) h (c i) a)
            ( fib-square (ind-Σ f) h cone-descent-Σ (pair i a))
            ( map-inv-compute-fib-tot (λ i → pr1 (c i)) (pair i a))
            ( triangle-descent-Σ i a)
            ( is-fiberwise-equiv-fib-square-is-pullback
              (f i) h (c i) (is-pb-c i) a)
            ( is-equiv-map-inv-compute-fib-tot (λ i → pr1 (c i)) (pair i a))))

  abstract
    descent-Σ' : 
      is-pullback (ind-Σ f) h cone-descent-Σ →
      ((i : I) → is-pullback (f i) h (c i))
    descent-Σ' is-pb-dsq i =
      is-pullback-is-fiberwise-equiv-fib-square (f i) h (c i)
        ( λ a → is-equiv-comp
          ( fib-square (f i) h (c i) a)
          ( fib-square (ind-Σ f) h cone-descent-Σ (pair i a))
          ( map-inv-compute-fib-tot (λ i → pr1 (c i)) (pair i a))
          ( triangle-descent-Σ i a)
          ( is-equiv-map-inv-compute-fib-tot (λ i → pr1 (c i)) (pair i a))
          ( is-fiberwise-equiv-fib-square-is-pullback
            ( ind-Σ f)
            ( h)
            ( cone-descent-Σ)
            ( is-pb-dsq)
            ( pair i a)))

-- Extra material

-- Homotopical squares

{- We consider the situation where we have two 'parallel squares', i.e. a
   diagram of the form

    TODO: FIX diagram

   Suppose that between each parallel pair of maps there is a homotopy, and
   that there is a homotopy between the homotopies that fill the two squares,
   as expessed by the type coherence-htpy-square below. Our goal is to show
   that if one of the squares is a pullback square, then so is the other.

   We do so without using function extensionality. -}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} 
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  coherence-htpy-square :
    {l4 : Level} {C : UU l4} (c : cone f g C) (c' : cone f' g' C)
    (Hp : pr1 c ~ pr1 c') (Hq : pr1 (pr2 c) ~ pr1 (pr2 c')) → UU _
  coherence-htpy-square c c' Hp Hq =
    let p  = pr1 c
        q  = pr1 (pr2 c)
        H  = pr2 (pr2 c)
        p' = pr1 c'
        q' = pr1 (pr2 c')
        H' = pr2 (pr2 c')
    in
    ( H ∙h ((g ·l Hq) ∙h (Hg ·r q'))) ~ (((f ·l Hp) ∙h (Hf ·r p')) ∙h H')

  fam-htpy-square :
    {l4 : Level} {C : UU l4}  (c : cone f g C) → (c' : cone f' g' C) →
    (pr1 c ~ pr1 c') → UU _
  fam-htpy-square c c' Hp =
    Σ ((pr1 (pr2 c)) ~ (pr1 (pr2 c'))) (coherence-htpy-square c c' Hp)
  
  htpy-square :
    {l4 : Level} {C : UU l4} →
    cone f g C → cone f' g' C → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
  htpy-square c c' = Σ ((pr1 c) ~ (pr1 c')) (fam-htpy-square c c')

  map-is-pullback-htpy :
    canonical-pullback f' g' → canonical-pullback f g
  map-is-pullback-htpy =
    tot (λ a → tot (λ b →
      ( concat' (f a) (inv (Hg b))) ∘ (concat (Hf a) (g' b))))

  abstract
    is-equiv-map-is-pullback-htpy :
      is-equiv map-is-pullback-htpy
    is-equiv-map-is-pullback-htpy =
      is-equiv-tot-is-fiberwise-equiv (λ a →
        is-equiv-tot-is-fiberwise-equiv (λ b →
          is-equiv-comp
            ( (concat' (f a) (inv (Hg b))) ∘ (concat (Hf a) (g' b)))
            ( concat' (f a) (inv (Hg b)))
            ( concat (Hf a) (g' b))
            ( refl-htpy)
            ( is-equiv-concat (Hf a) (g' b))
            ( is-equiv-concat' (f a) (inv (Hg b)))))

  triangle-is-pullback-htpy :
    {l4 : Level} {C : UU l4}
    {c : cone f g C} {c' : cone f' g' C} (Hc : htpy-square c c') →
    (gap f g c) ~ (map-is-pullback-htpy ∘ (gap f' g' c'))
  triangle-is-pullback-htpy
    {c = pair p (pair q H)} {pair p' (pair q' H')} (pair Hp (pair Hq HH)) z =
    map-extensionality-canonical-pullback f g
      ( Hp z)
      ( Hq z)
      ( ( inv
          ( assoc (ap f (Hp z)) ((Hf (p' z)) ∙ (H' z)) (inv (Hg (q' z))))) ∙
        ( inv
          ( con-inv
            ( (H z) ∙ (ap g (Hq z)))
            ( Hg (q' z))
            ( ( ap f (Hp z)) ∙ ((Hf (p' z)) ∙ (H' z)))
            ( ( assoc (H z) (ap g (Hq z)) (Hg (q' z))) ∙
              ( ( HH z) ∙
                ( assoc (ap f (Hp z)) (Hf (p' z)) (H' z)))))))

  abstract
    is-pullback-htpy :
      {l4 : Level} {C : UU l4}
      {c : cone f g C} (c' : cone f' g' C) (Hc : htpy-square c c') →
      is-pullback f' g' c' → is-pullback f g c
    is-pullback-htpy
      {c = pair p (pair q H)} (pair p' (pair q' H'))
      (pair Hp (pair Hq HH)) is-pb-c' =
      is-equiv-comp
        ( gap f g (triple p q H))
        ( map-is-pullback-htpy)
        ( gap f' g' (triple p' q' H'))
        ( triangle-is-pullback-htpy
          {c = triple p q H} {triple p' q' H'} (triple Hp Hq HH))
        ( is-pb-c')
        ( is-equiv-map-is-pullback-htpy)

  abstract
    is-pullback-htpy' :
      {l4 : Level} {C : UU l4}
      (c : cone f g C) {c' : cone f' g' C} (Hc : htpy-square c c') →
      is-pullback f g c → is-pullback f' g' c'
    is-pullback-htpy'
      (pair p (pair q H)) {pair p' (pair q' H')}
      (pair Hp (pair Hq HH)) is-pb-c =
      is-equiv-right-factor
        ( gap f g (triple p q H))
        ( map-is-pullback-htpy)
        ( gap f' g' (triple p' q' H'))
        ( triangle-is-pullback-htpy
          {c = triple p q H} {triple p' q' H'} (triple Hp Hq HH))
        ( is-equiv-map-is-pullback-htpy)
        ( is-pb-c)

{- In the following part we will relate the type htpy-square to the Identity
   type of cones. Here we will rely on function extensionality. -}

refl-htpy-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  htpy-square (refl-htpy {f = f}) (refl-htpy {f = g}) c c
refl-htpy-square f g c =
  triple refl-htpy refl-htpy right-unit-htpy

htpy-eq-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  Id c c' → htpy-square (refl-htpy {f = f}) (refl-htpy {f = g}) c c'
htpy-eq-square f g c .c refl =
  triple refl-htpy refl-htpy right-unit-htpy

htpy-square-refl-htpy-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) →
  (c c' : cone f g C) →
  htpy-cone f g c c' → htpy-square (refl-htpy {f = f}) (refl-htpy {f = g}) c c'
htpy-square-refl-htpy-htpy-cone f g
  (pair p (pair q H)) (pair p' (pair q' H')) =
  tot
    ( λ K → tot
      ( λ L M → ( ap-concat-htpy H _ _ right-unit-htpy) ∙h
        ( M ∙h ap-concat-htpy' _ _ H' (inv-htpy right-unit-htpy))))

abstract
  is-equiv-htpy-square-refl-htpy-htpy-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) →
    (c c' : cone f g C) →
    is-equiv (htpy-square-refl-htpy-htpy-cone f g c c')
  is-equiv-htpy-square-refl-htpy-htpy-cone f g
    (pair p (pair q H)) (pair p' (pair q' H')) =
    is-equiv-tot-is-fiberwise-equiv
      ( λ K → is-equiv-tot-is-fiberwise-equiv
        ( λ L → is-equiv-comp
          ( λ M → ( ap-concat-htpy H _ _ right-unit-htpy) ∙h
            ( M ∙h
              ( ap-concat-htpy' _ _ H' (inv-htpy right-unit-htpy))))
          ( concat-htpy
            ( ap-concat-htpy H _ _ right-unit-htpy)
            ( ((f ·l K) ∙h refl-htpy) ∙h H'))
          ( concat-htpy'
            ( H ∙h (g ·l L))
            ( ap-concat-htpy' _ _ H' (inv-htpy right-unit-htpy)))
          ( refl-htpy)
          ( is-equiv-concat-htpy'
            ( H ∙h (g ·l L))
            ( λ x → ap (λ z → z ∙ H' x) (inv right-unit)))
          ( is-equiv-concat-htpy
            ( λ x → ap (_∙_ (H x)) right-unit)
            ( ((f ·l K) ∙h refl-htpy) ∙h H'))))

abstract
  is-contr-total-htpy-square-refl-htpy-refl-htpy :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) →
    (c : cone f g C) →
    is-contr (Σ (cone f g C) (htpy-square (refl-htpy' f) (refl-htpy' g) c))
  is-contr-total-htpy-square-refl-htpy-refl-htpy {A = A} {B} {X} {C}
    f g (pair p (pair q H)) =
    let c = triple p q H in
    is-contr-is-equiv'
      ( Σ (cone f g C) (htpy-cone f g c))
      ( tot (htpy-square-refl-htpy-htpy-cone f g c))
      ( is-equiv-tot-is-fiberwise-equiv
        ( is-equiv-htpy-square-refl-htpy-htpy-cone f g c))
      ( is-contr-total-htpy-cone f g c)

abstract
  is-contr-total-htpy-square-refl-htpy :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) →
    is-contr (Σ (cone f g' C) (htpy-square (refl-htpy' f) Hg c))
  is-contr-total-htpy-square-refl-htpy {C = C} f {g} =
    ind-htpy g
      ( λ g'' Hg' → ( c : cone f g C) →
        is-contr (Σ (cone f g'' C) (htpy-square (refl-htpy' f) Hg' c)))
      ( is-contr-total-htpy-square-refl-htpy-refl-htpy f g)

abstract
  is-contr-total-htpy-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) →
    is-contr (Σ (cone f' g' C) (htpy-square Hf Hg c))
  is-contr-total-htpy-square {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg =
    ind-htpy
      { A = A}
      { B = λ t → X}
      ( f)
      ( λ f'' Hf' → (g g' : B → X) (Hg : g ~ g') (c : cone f g C) →
        is-contr (Σ (cone f'' g' C) (htpy-square Hf' Hg c)))
      ( λ g g' Hg → is-contr-total-htpy-square-refl-htpy f Hg)
      Hf g g' Hg

tr-tr-refl-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy (refl-htpy {f = f})) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (refl-htpy {f = g})) tr-c
  in
  Id tr-tr-c c
tr-tr-refl-htpy-cone {C = C} f g c =
  let tr-c = tr (λ f''' → cone f''' g C) (eq-htpy refl-htpy) c
      tr-tr-c = tr (λ g'' → cone f g'' C) (eq-htpy refl-htpy) tr-c
      α : Id tr-tr-c tr-c
      α = ap (λ t → tr (λ g'' → cone f g'' C) t tr-c) (eq-htpy-refl-htpy g)
      β : Id tr-c c
      β = ap (λ t → tr (λ f''' → cone f''' g C) t c) (eq-htpy-refl-htpy f)
  in
  α ∙ β

htpy-eq-square-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy (refl-htpy {f = f})) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (refl-htpy {f = g})) tr-c
  in
  Id tr-tr-c c' → htpy-square (refl-htpy' f) (refl-htpy' g) c c'
htpy-eq-square-refl-htpy f g c c' =
  ind-is-equiv
    ( λ p → htpy-square (refl-htpy' f) (refl-htpy' g) c c')
    ( λ (p : Id c c') → (tr-tr-refl-htpy-cone f g c) ∙ p)
    ( is-equiv-concat (tr-tr-refl-htpy-cone f g c) c')
    ( htpy-eq-square f g c c')

comp-htpy-eq-square-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  ( (htpy-eq-square-refl-htpy f g c c') ∘
    (concat (tr-tr-refl-htpy-cone f g c) c')) ~
  ( htpy-eq-square f g c c')
comp-htpy-eq-square-refl-htpy f g c c' =
  htpy-comp-is-equiv
    ( λ p → htpy-square (refl-htpy' f) (refl-htpy' g) c c')
    ( λ (p : Id c c') → (tr-tr-refl-htpy-cone f g c) ∙ p)
    ( is-equiv-concat (tr-tr-refl-htpy-cone f g c) c')
    ( htpy-eq-square f g c c')

abstract
  htpy-square-eq' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f g' C) →
    let tr-c    = tr (λ x → cone x g C) (eq-htpy (refl-htpy {f = f})) c
        tr-tr-c = tr (λ y → cone f y C) (eq-htpy Hg) tr-c
    in
    Id tr-tr-c c' → htpy-square (refl-htpy' f) Hg c c'
  htpy-square-eq' {C = C} f {g} =
    ind-htpy g
      ( λ g'' Hg' →
        ( c : cone f g C) (c' : cone f g'' C) →
        Id (tr (λ g'' → cone f g'' C) (eq-htpy Hg')
          ( tr (λ f''' → cone f''' g C) (eq-htpy (refl-htpy' f)) c)) c' →
        htpy-square refl-htpy Hg' c c')
      ( htpy-eq-square-refl-htpy f g)

  comp-htpy-square-eq' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c c' : cone f g C) →
    ( ( htpy-square-eq' f refl-htpy c c') ∘
      ( concat (tr-tr-refl-htpy-cone f g c) c')) ~
    ( htpy-eq-square f g c c')
  comp-htpy-square-eq' {A = A} {B} {X} {C} f g c c' =
    htpy-right-whisk
      ( htpy-eq (htpy-eq (htpy-eq (comp-htpy g
        ( λ g'' Hg' →
          ( c : cone f g C) (c' : cone f g'' C) →
            Id (tr (λ g'' → cone f g'' C) (eq-htpy Hg')
              ( tr (λ f''' → cone f''' g C) (eq-htpy (refl-htpy' f)) c)) c' →
          htpy-square refl-htpy Hg' c c')
      ( htpy-eq-square-refl-htpy f g)) c) c'))
      ( concat (tr-tr-refl-htpy-cone f g c) c') ∙h
    ( comp-htpy-eq-square-refl-htpy f g c c')

abstract
  htpy-square-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    let tr-c    = tr (λ x → cone x g C) (eq-htpy Hf) c
        tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
    in
    Id tr-tr-c c' → htpy-square Hf Hg c c'
  htpy-square-eq {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' p =
    ind-htpy f
    ( λ f'' Hf' →
      ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
      ( Id (tr (λ g'' → cone f'' g'' C) (eq-htpy Hg)
        ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c)) c') →
      htpy-square Hf' Hg c c')
    ( λ g g' → htpy-square-eq' f {g = g} {g' = g'})
    Hf g g' Hg c c' p
  
  comp-htpy-square-eq : 
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c c' : cone f g C) →
    ( ( htpy-square-eq refl-htpy refl-htpy c c') ∘
      ( concat (tr-tr-refl-htpy-cone f g c) c')) ~
    ( htpy-eq-square f g c c')
  comp-htpy-square-eq {A = A} {B} {X} {C} f g c c' =
    htpy-right-whisk
      ( htpy-eq (htpy-eq (htpy-eq (htpy-eq (htpy-eq (htpy-eq (comp-htpy f
        ( λ f'' Hf' →
          ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
            ( Id ( tr (λ g'' → cone f'' g'' C) (eq-htpy Hg)
                 ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c)) c') →
            htpy-square Hf' Hg c c')
        ( λ g g' → htpy-square-eq' f {g = g} {g' = g'})) g) g)
        refl-htpy) c) c'))
      ( concat (tr-tr-refl-htpy-cone f g c) c') ∙h
      ( comp-htpy-square-eq' f g c c')

abstract
  is-fiberwise-equiv-htpy-square-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    is-equiv (htpy-square-eq Hf Hg c c')
  is-fiberwise-equiv-htpy-square-eq
    {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' =
    ind-htpy f
      ( λ f' Hf →
        ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f' g' C) →
          is-equiv (htpy-square-eq Hf Hg c c'))
      ( λ g g' Hg c c' →
        ind-htpy g
          ( λ g' Hg →
            ( c : cone f g C) (c' : cone f g' C) →
              is-equiv (htpy-square-eq refl-htpy Hg c c'))
          ( λ c c' →
            is-equiv-left-factor
              ( htpy-eq-square f g c c')
              ( htpy-square-eq refl-htpy refl-htpy c c')
              ( concat (tr-tr-refl-htpy-cone f g c) c')
              ( inv-htpy (comp-htpy-square-eq f g c c'))
              ( fundamental-theorem-id c
                ( refl-htpy-square f g c)
                ( is-contr-total-htpy-square (refl-htpy' f) (refl-htpy' g) c)
                ( htpy-eq-square f g c) c')
              ( is-equiv-concat (tr-tr-refl-htpy-cone f g c) c'))
          Hg c c')
      Hf g g' Hg c c'

eq-htpy-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f' g' C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy Hf) c
      tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
  in
  htpy-square Hf Hg c c' → Id tr-tr-c c'
eq-htpy-square Hf Hg c c' =
  map-inv-is-equiv
    { f = htpy-square-eq Hf Hg c c'}
    ( is-fiberwise-equiv-htpy-square-eq Hf Hg c c')

-- Exercises

-- Exercise 10.1

cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  cone (const unit A x) (const unit A y) (Id x y)
cone-Id x y =
  triple (const (Id x y) unit star) (const (Id x y) unit star) id

inv-gap-cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  canonical-pullback (const unit A x) (const unit A y) → Id x y
inv-gap-cone-Id x y (pair star (pair star p)) = p

abstract
  issec-inv-gap-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    ( ( gap (const unit A x) (const unit A y) (cone-Id x y)) ∘
      ( inv-gap-cone-Id x y)) ~ id
  issec-inv-gap-cone-Id x y (pair star (pair star p)) = refl

abstract
  isretr-inv-gap-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    ( ( inv-gap-cone-Id x y) ∘
      ( gap (const unit A x) (const unit A y) (cone-Id x y))) ~ id
  isretr-inv-gap-cone-Id x y p = refl

abstract
  is-pullback-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    is-pullback (const unit A x) (const unit A y) (cone-Id x y)
  is-pullback-cone-Id x y =
    is-equiv-has-inverse
      ( inv-gap-cone-Id x y)
      ( issec-inv-gap-cone-Id x y)
      ( isretr-inv-gap-cone-Id x y)

{- One way to solve this exercise is to show that Id (pr1 t) (pr2 t) is a
   pullback for every t : A × A. This allows one to use path induction to
   show that the inverse of the gap map is a section.
-}

cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  cone (const unit (A × A) t) (diagonal A) (Id (pr1 t) (pr2 t))
cone-Id' {A = A} (pair x y) =
  triple
    ( const (Id x y) unit star)
    ( const (Id x y) A x)
    ( λ p → eq-pair-Σ refl (inv p))

inv-gap-cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  canonical-pullback (const unit (A × A) t) (diagonal A) → Id (pr1 t) (pr2 t)
inv-gap-cone-Id' t (pair star (pair z p)) =
  (ap pr1 p) ∙ (inv (ap pr2 p))

abstract
  issec-inv-gap-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    ( ( gap (const unit (A × A) t) (diagonal A) (cone-Id' t)) ∘
      ( inv-gap-cone-Id' t)) ~ id
  issec-inv-gap-cone-Id' .(pair z z) (pair star (pair z refl)) = refl

abstract
  isretr-inv-gap-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    ( ( inv-gap-cone-Id' t) ∘
      ( gap (const unit (A × A) t) (diagonal A) (cone-Id' t))) ~ id
  isretr-inv-gap-cone-Id' (pair x .x) refl = refl

abstract
  is-pullback-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    is-pullback (const unit (A × A) t) (diagonal A) (cone-Id' t)
  is-pullback-cone-Id' t =
    is-equiv-has-inverse
      ( inv-gap-cone-Id' t)
      ( issec-inv-gap-cone-Id' t)
      ( isretr-inv-gap-cone-Id' t)

-- Exercise 10.2

diagonal-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  A → canonical-pullback f f
diagonal-map f x = triple x x refl

fib-ap-fib-diagonal-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : canonical-pullback f f) →
  (fib (diagonal-map f) t) → (fib (ap f) (pr2 (pr2 t)))
pr1 (fib-ap-fib-diagonal-map f .(diagonal-map f z) (pair z refl)) = refl
pr2 (fib-ap-fib-diagonal-map f .(diagonal-map f z) (pair z refl)) = refl

fib-diagonal-map-fib-ap :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : canonical-pullback f f) →
  (fib (ap f) (pr2 (pr2 t))) → (fib (diagonal-map f) t)
pr1
  ( fib-diagonal-map-fib-ap f
    ( pair x (pair .x .(ap f refl)))
    ( pair refl refl)) = x
pr2 (fib-diagonal-map-fib-ap f
  ( pair x (pair .x .(ap f refl)))
  ( pair refl refl)) = refl

abstract
  issec-fib-diagonal-map-fib-ap :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : canonical-pullback f f) →
    ((fib-ap-fib-diagonal-map f t) ∘ (fib-diagonal-map-fib-ap f t)) ~ id
  issec-fib-diagonal-map-fib-ap f (pair x (pair .x .refl)) (pair refl refl) =
    refl

abstract
  isretr-fib-diagonal-map-fib-ap :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : canonical-pullback f f) →
    ((fib-diagonal-map-fib-ap f t) ∘ (fib-ap-fib-diagonal-map f t)) ~ id
  isretr-fib-diagonal-map-fib-ap f .(pair x (pair x refl)) (pair x refl) =
    refl

abstract
  is-equiv-fib-ap-fib-diagonal-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : canonical-pullback f f) →
    is-equiv (fib-ap-fib-diagonal-map f t)
  is-equiv-fib-ap-fib-diagonal-map f t =
    is-equiv-has-inverse
      ( fib-diagonal-map-fib-ap f t)
      ( issec-fib-diagonal-map-fib-ap f t)
      ( isretr-fib-diagonal-map-fib-ap f t)

abstract
  is-trunc-diagonal-map-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map (succ-𝕋 k) f → is-trunc-map k (diagonal-map f)
  is-trunc-diagonal-map-is-trunc-map k f is-trunc-f (pair x (pair y p)) =
    is-trunc-is-equiv k (fib (ap f) p)
      ( fib-ap-fib-diagonal-map f (triple x y p))
      ( is-equiv-fib-ap-fib-diagonal-map f (triple x y p))
      ( is-trunc-map-ap-is-trunc-map k f is-trunc-f x y p)

abstract
  is-trunc-map-is-trunc-diagonal-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map k (diagonal-map f) → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-is-trunc-diagonal-map
    k f is-trunc-δ b (pair x p) (pair x' p') =
    is-trunc-is-equiv k
      ( fib (ap f) (p ∙ (inv p')))
      ( fib-ap-eq-fib f (pair x p) (pair x' p'))
      ( is-equiv-fib-ap-eq-fib f (pair x p) (pair x' p'))
      ( is-trunc-is-equiv' k
        ( fib (diagonal-map f) (triple x x' (p ∙ (inv p'))))
        ( fib-ap-fib-diagonal-map f (triple x x' (p ∙ (inv p'))))
        ( is-equiv-fib-ap-fib-diagonal-map f (triple x x' (p ∙ (inv p'))))
        ( is-trunc-δ (triple x x' (p ∙ (inv p')))))

abstract
  is-equiv-diagonal-map-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-equiv (diagonal-map f)
  is-equiv-diagonal-map-is-emb f is-emb-f =
    is-equiv-is-contr-map
      ( is-trunc-diagonal-map-is-trunc-map neg-two-𝕋 f
        ( is-prop-map-is-emb is-emb-f))

abstract
  is-emb-is-equiv-diagonal-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (diagonal-map f) → is-emb f
  is-emb-is-equiv-diagonal-map f is-equiv-δ =
    is-emb-is-prop-map
      ( is-trunc-map-is-trunc-diagonal-map neg-two-𝕋 f
        ( is-contr-map-is-equiv is-equiv-δ))

-- Exercise 10.3

cone-swap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) → cone f g C → cone g f C
cone-swap f g (pair p (pair q H)) = triple q p (inv-htpy H)

map-canonical-pullback-swap :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → canonical-pullback f g → canonical-pullback g f
map-canonical-pullback-swap f g (pair a (pair b p)) =
  triple b a (inv p)

inv-inv-map-canonical-pullback-swap :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  (map-canonical-pullback-swap f g ∘ map-canonical-pullback-swap g f) ~ id
inv-inv-map-canonical-pullback-swap f g (pair b (pair a q)) =
  eq-pair-Σ refl (eq-pair-Σ refl (inv-inv q))

abstract
  is-equiv-map-canonical-pullback-swap :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-canonical-pullback-swap f g)
  is-equiv-map-canonical-pullback-swap f g =
    is-equiv-has-inverse
      ( map-canonical-pullback-swap g f)
      ( inv-inv-map-canonical-pullback-swap f g)
      ( inv-inv-map-canonical-pullback-swap g f)

triangle-map-canonical-pullback-swap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( gap g f (cone-swap f g c)) ~
  ( ( map-canonical-pullback-swap f g) ∘ ( gap f g c))
triangle-map-canonical-pullback-swap f g (pair p (pair q H)) x = refl

abstract
  is-pullback-cone-swap :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-pullback g f (cone-swap f g c)
  is-pullback-cone-swap f g c is-pb-c =
    is-equiv-comp
      ( gap g f (cone-swap f g c))
      ( map-canonical-pullback-swap f g)
      ( gap f g c)
      ( triangle-map-canonical-pullback-swap f g c)
      ( is-pb-c)
      ( is-equiv-map-canonical-pullback-swap f g)

abstract
  is-pullback-cone-swap' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback g f (cone-swap f g c) → is-pullback f g c
  is-pullback-cone-swap' f g c is-pb-c' =
    is-equiv-right-factor
      ( gap g f (cone-swap f g c))
      ( map-canonical-pullback-swap f g)
      ( gap f g c)
      ( triangle-map-canonical-pullback-swap f g c)
      ( is-equiv-map-canonical-pullback-swap f g)
      ( is-pb-c')

{- We conclude the swapped versions of some properties derived above, for 
   future convenience -}

abstract
  is-trunc-is-pullback' :
    {l1 l2 l3 l4 : Level} (k : 𝕋)
    {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-trunc-map k f → is-trunc-map k (pr1 (pr2 c))
  is-trunc-is-pullback' k f g (pair p (pair q H)) pb is-trunc-f =
    is-trunc-is-pullback k g f
      ( cone-swap f g (triple p q H))
      ( is-pullback-cone-swap f g (triple p q H) pb)
      is-trunc-f

abstract
  is-emb-is-pullback' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-emb f → is-emb (pr1 (pr2 c))
  is-emb-is-pullback' f g c pb is-emb-f =
    is-emb-is-prop-map
      ( is-trunc-is-pullback' neg-one-𝕋 f g c pb
        ( is-prop-map-is-emb is-emb-f))

abstract
  is-equiv-is-pullback' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-equiv f → is-pullback f g c → is-equiv (pr1 (pr2 c))
  is-equiv-is-pullback' f g c is-equiv-f pb =
    is-equiv-is-contr-map
      ( is-trunc-is-pullback' neg-two-𝕋 f g c pb
        ( is-contr-map-is-equiv is-equiv-f))

abstract
  is-pullback-is-equiv' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-equiv f → is-equiv (pr1 (pr2 c)) → is-pullback f g c
  is-pullback-is-equiv' f g (pair p (pair q H)) is-equiv-f is-equiv-q =
    is-pullback-cone-swap' f g (triple p q H)
      ( is-pullback-is-equiv g f
        ( cone-swap f g (triple p q H))
        is-equiv-f
        is-equiv-q)

-- Exercise 10.4

cone-empty :
  {l1 l2 l3 : Level} {B : UU l1} {X : UU l2} {C : UU l3} →
  (g : B → X) (p : C → empty) (q : C → B) →
  cone ex-falso g C
cone-empty g p q = triple p q (λ c → ex-falso (p c))

abstract
  descent-empty :
    {l1 l2 l3 : Level} {B : UU l1} {X : UU l2} {C : UU l3} →
    (g : B → X) (c : cone ex-falso g C) → is-pullback ex-falso g c
  descent-empty g c =
    is-pullback-is-fiberwise-equiv-fib-square _ g c ind-empty

abstract
  descent-empty' :
    {l1 l2 l3 : Level} {B : UU l1} {X : UU l2} {C : UU l3} →
    (g : B → X) (p : C → empty) (q : C → B) →
    is-pullback ex-falso g (cone-empty g p q)
  descent-empty' g p q = descent-empty g (cone-empty g p q)

-- Exercise 10.5

{- We show that a square is a pullback square if and only if every exponent of 
  it is a pullback square. -}

cone-exponent :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} (T : UU l5)
  (f : A → X) (g : B → X) (c : cone f g C) →
  cone (λ (h : T → A) → f ∘ h) (λ (h : T → B) → g ∘ h) (T → C)
cone-exponent T f g (pair p (pair q H)) =
  triple
    ( λ h → p ∘ h)
    ( λ h → q ∘ h)
    ( λ h → eq-htpy (H ·r h))

map-canonical-pullback-exponent :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  (T : UU l4) →
  canonical-pullback (λ (h : T → A) → f ∘ h) (λ (h : T → B) → g ∘ h) →
  cone f g T
map-canonical-pullback-exponent f g T =
  tot (λ p → tot (λ q → htpy-eq))

abstract
  is-equiv-map-canonical-pullback-exponent :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
    (T : UU l4) → is-equiv (map-canonical-pullback-exponent f g T)
  is-equiv-map-canonical-pullback-exponent f g T =
    is-equiv-tot-is-fiberwise-equiv
      ( λ p → is-equiv-tot-is-fiberwise-equiv
        ( λ q → funext (f ∘ p) (g ∘ q)))

triangle-map-canonical-pullback-exponent :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (T : UU l5) (f : A → X) (g : B → X) (c : cone f g C) →
  ( cone-map f g {C' = T} c) ~
  ( ( map-canonical-pullback-exponent f g T) ∘
    ( gap
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( cone-exponent T f g c)))
triangle-map-canonical-pullback-exponent
  {A = A} {B} T f g (pair p (pair q H)) h =
  eq-pair-Σ refl (eq-pair-Σ refl (inv (issec-eq-htpy (H ·r h))))

abstract
  is-pullback-exponent-is-pullback :
    {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
    (T : UU l5) →
    is-pullback
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( cone-exponent T f g c)
  is-pullback-exponent-is-pullback f g c is-pb-c T =
    is-equiv-right-factor
      ( cone-map f g c)
      ( map-canonical-pullback-exponent f g T)
      ( gap (_∘_ f) (_∘_ g) (cone-exponent T f g c))
      ( triangle-map-canonical-pullback-exponent T f g c)
      ( is-equiv-map-canonical-pullback-exponent f g T)
      ( universal-property-pullback-is-pullback f g c is-pb-c T)

abstract
  is-pullback-is-pullback-exponent :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    ((l5 : Level) (T : UU l5) → is-pullback
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( cone-exponent T f g c)) →
    is-pullback f g c
  is-pullback-is-pullback-exponent f g c is-pb-exp =
    is-pullback-universal-property-pullback f g c
      ( λ T → is-equiv-comp
        ( cone-map f g c)
        ( map-canonical-pullback-exponent f g T)
        ( gap (_∘_ f) (_∘_ g) (cone-exponent T f g c))
        ( triangle-map-canonical-pullback-exponent T f g c)
        ( is-pb-exp _ T)
        ( is-equiv-map-canonical-pullback-exponent f g T))

-- Exercise 10.6

{- Note: the solution below involves a substantial amount of path algebra. It
   would be nice to find a simpler solution.
   -}

cone-fold :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) →
  cone f g C → cone (map-prod f g) (diagonal X) C
cone-fold f g (pair p (pair q H)) =
  triple (λ z → pair (p z) (q z)) (g ∘ q) (λ z → eq-pair (H z) refl)

map-cone-fold :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} 
  (f : A → X) → (g : B → X) →
  canonical-pullback f g → canonical-pullback (map-prod f g) (diagonal X)
map-cone-fold f g (pair a (pair b p)) =
  triple (pair a b) (g b) (eq-pair p refl)

inv-map-cone-fold :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} 
  (f : A → X) → (g : B → X) →
  canonical-pullback (map-prod f g) (diagonal X) → canonical-pullback f g
inv-map-cone-fold f g (pair (pair a b) (pair x α)) =
  triple a b ((ap pr1 α) ∙ (inv (ap pr2 α)))

ap-diagonal :
  {l : Level} {A : UU l} {x y : A} (p : Id x y) →
  Id (ap (diagonal A) p) (eq-pair p p)
ap-diagonal refl = refl

eq-pair-concat :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x x' x'' : A} {y y' y'' : B}
  (p : Id x x') (p' : Id x' x'') (q : Id y y') (q' : Id y' y'') →
  Id ( eq-pair {s = pair x y} {t = pair x'' y''} (p ∙ p') (q ∙ q'))
    ( ( eq-pair {s = pair x y} {t = pair x' y'} p q) ∙
      ( eq-pair p' q'))
eq-pair-concat refl p' refl q' = refl

abstract
  issec-inv-map-cone-fold :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) →
    ((map-cone-fold f g) ∘ (inv-map-cone-fold f g)) ~ id
  issec-inv-map-cone-fold {A = A} {B} {X} f g (pair (pair a b) (pair x α)) =
    map-extensionality-canonical-pullback
      ( map-prod f g)
      ( diagonal X)
      refl
      ( ap pr2 α)
      ( ( ( ( inv (issec-pair-eq α)) ∙
            ( ap
              ( λ t → (eq-pair t (ap pr2 α)))
              ( ( ( inv right-unit) ∙
                  ( inv (ap (concat (ap pr1 α) x) (left-inv (ap pr2 α))))) ∙
                ( inv (assoc (ap pr1 α) (inv (ap pr2 α)) (ap pr2 α)))))) ∙
          ( eq-pair-concat
            ( (ap pr1 α) ∙ (inv (ap pr2 α)))
            ( ap pr2 α)
            ( refl)
            ( ap pr2 α))) ∙
        ( ap
          ( concat
            ( eq-pair ((ap pr1 α) ∙ (inv (ap pr2 α))) refl)
            ( pair x x))
          ( inv (ap-diagonal (ap pr2 α)))))

ap-pr1-eq-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') →
  Id (ap pr1 (eq-pair {s = pair x y} {pair x' y'} p q)) p
ap-pr1-eq-pair refl refl = refl

ap-pr2-eq-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') →
  Id (ap pr2 (eq-pair {s = pair x y} {pair x' y'} p q)) q
ap-pr2-eq-pair refl refl = refl

abstract
  isretr-inv-map-cone-fold :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) →
    ((inv-map-cone-fold f g) ∘ (map-cone-fold f g)) ~ id
  isretr-inv-map-cone-fold { A = A} { B = B} { X = X} f g (pair a (pair b p)) =
    map-extensionality-canonical-pullback {A = A} {B = B} {X = X} f g
      refl
      refl
      ( inv
        ( ( ap
            ( concat' (f a) refl)
            ( ( ( ap
                  ( λ t → t ∙
                    ( inv
                      ( ap pr2 (eq-pair
                      { s = pair (f a) (g b)}
                      { pair (g b) (g b)}
                      p refl))))
                    ( ap-pr1-eq-pair p refl)) ∙
                ( ap (λ t → p ∙ (inv t)) (ap-pr2-eq-pair p refl))) ∙
              ( right-unit))) ∙
          ( right-unit)))
  
abstract
  is-equiv-map-cone-fold :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-cone-fold f g)
  is-equiv-map-cone-fold f g =
    is-equiv-has-inverse
      ( inv-map-cone-fold f g)
      ( issec-inv-map-cone-fold f g)
      ( isretr-inv-map-cone-fold f g)

triangle-map-cone-fold :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( gap (map-prod f g) (diagonal X) (cone-fold f g c)) ~
  ( (map-cone-fold f g) ∘ (gap f g c))
triangle-map-cone-fold f g (pair p (pair q H)) z = refl

abstract
  is-pullback-cone-fold-is-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c →
    is-pullback (map-prod f g) (diagonal X) (cone-fold f g c)
  is-pullback-cone-fold-is-pullback f g c is-pb-c =
    is-equiv-comp
      ( gap (map-prod f g) (diagonal _) (cone-fold f g c))
      ( map-cone-fold f g)
      ( gap f g c)
      ( triangle-map-cone-fold f g c)
      ( is-pb-c)
      ( is-equiv-map-cone-fold f g)

abstract
  is-pullback-is-pullback-cone-fold :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback (map-prod f g) (diagonal X) (cone-fold f g c) →
    is-pullback f g c
  is-pullback-is-pullback-cone-fold f g c is-pb-fold =
    is-equiv-right-factor
      ( gap (map-prod f g) (diagonal _) (cone-fold f g c))
      ( map-cone-fold f g)
      ( gap f g c)
      ( triangle-map-cone-fold f g c)
      ( is-equiv-map-cone-fold f g)
      ( is-pb-fold)

-- Exercise 10.7

cone-pair :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  cone f g C → cone f' g' C' →
  cone (map-prod f f') (map-prod g g') (C × C')
cone-pair f g f' g' (pair p (pair q H)) (pair p' (pair q' H')) =
  triple
    ( map-prod p p')
    ( map-prod q q')
    ( ( inv-htpy (map-prod-comp p p' f f')) ∙h
      ( ( htpy-map-prod H H') ∙h
        ( map-prod-comp q q' g g')))

map-cone-pair' :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  (t : A × A') (s : B × B') →
  (Id (f (pr1 t)) (g (pr1 s))) × (Id (f' (pr2 t)) (g' (pr2 s))) →
  (Id (pr1 (map-prod f f' t)) (pr1 (map-prod g g' s))) ×
  (Id (pr2 (map-prod f f' t)) (pr2 (map-prod g g' s)))
map-cone-pair' f g f' g' (pair a a') (pair b b') = id

abstract
  is-equiv-map-cone-pair' :
    {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
    (t : A × A') (s : B × B') →
    is-equiv (map-cone-pair' f g f' g' t s)
  is-equiv-map-cone-pair' f g f' g' (pair a a') (pair b b') = is-equiv-id

map-cone-pair :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  (canonical-pullback f g) × (canonical-pullback f' g') →
  canonical-pullback (map-prod f f') (map-prod g g')
map-cone-pair {A' = A'} {B'} f g f' g' =
  ( tot
    ( λ t →
      ( tot
        ( λ s →
          ( eq-pair' ∘ (map-cone-pair' f g f' g' t s)))) ∘
      ( map-interchange-Σ-Σ (λ y p y' → Id (f' (pr2 t)) (g' y'))))) ∘
  ( map-interchange-Σ-Σ (λ x t x' → Σ _ (λ y' → Id (f' x') (g' y'))))

triangle-map-cone-pair :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (c : cone f g C)
  (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
  (gap (map-prod f f') (map-prod g g') (cone-pair f g f' g' c c')) ~
  ((map-cone-pair f g f' g') ∘ (map-prod (gap f g c) (gap f' g' c')))
triangle-map-cone-pair
  f g (pair p (pair q H)) f' g' (pair p' (pair q' H')) (pair z z') =
  eq-pair-Σ refl (eq-pair-Σ refl right-unit)

abstract
  is-equiv-map-cone-pair :
    {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
    is-equiv (map-cone-pair f g f' g')
  is-equiv-map-cone-pair f g f' g' =
    is-equiv-comp
      ( map-cone-pair f g f' g')
      ( tot ( λ t →
        ( tot
          ( λ s →
            ( eq-pair' ∘ (map-cone-pair' f g f' g' t s)))) ∘
        ( map-interchange-Σ-Σ _)))
      ( map-interchange-Σ-Σ _)
      ( refl-htpy)
      ( is-equiv-map-interchange-Σ-Σ _)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ t → is-equiv-comp
          ( ( tot
              ( λ s →
                ( eq-pair' ∘ (map-cone-pair' f g f' g' t s)))) ∘
            ( map-interchange-Σ-Σ
              ( λ y p y' → Id (f' (pr2 t)) (g' y'))))
          ( tot
            ( λ s →
              ( eq-pair' ∘ (map-cone-pair' f g f' g' t s))))
          ( map-interchange-Σ-Σ
            ( λ y p y' → Id (f' (pr2 t)) (g' y')))
          ( refl-htpy)
          ( is-equiv-map-interchange-Σ-Σ _)
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ s → is-equiv-comp
              ( eq-pair' ∘ (map-cone-pair' f g f' g' t s))
              ( eq-pair')
              ( map-cone-pair' f g f' g' t s)
              ( refl-htpy)
              ( is-equiv-map-cone-pair' f g f' g' t s)
              ( is-equiv-eq-pair
                ( map-prod f f' t)
                ( map-prod g g' s))))))

abstract
  is-pullback-prod-is-pullback-pair :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback f g c → is-pullback f' g' c' →
    is-pullback
      ( map-prod f f') (map-prod g g') (cone-pair f g f' g' c c')
  is-pullback-prod-is-pullback-pair f g c f' g' c' is-pb-c is-pb-c' =
    is-equiv-comp
      ( gap (map-prod f f') (map-prod g g') (cone-pair f g f' g' c c'))
      ( map-cone-pair f g f' g')
      ( map-prod (gap f g c) (gap f' g' c'))
      ( triangle-map-cone-pair f g c f' g' c')
      ( is-equiv-map-prod _ _ is-pb-c is-pb-c')
      ( is-equiv-map-cone-pair f g f' g')
  
map-fib-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) (t : C × D) →
  fib (map-prod f g) t → (fib f (pr1 t)) × (fib g (pr2 t))
pr1
  ( pr1
    ( map-fib-map-prod f g .(map-prod f g (pair a b))
      ( pair (pair a b) refl))) = a
pr2
  ( pr1
    ( map-fib-map-prod f g .(map-prod f g (pair a b))
      ( pair (pair a b) refl))) = refl
pr1
  ( pr2
    ( map-fib-map-prod f g .(map-prod f g (pair a b))
      ( pair (pair a b) refl))) = b
pr2
  ( pr2
    ( map-fib-map-prod f g .(map-prod f g (pair a b))
      ( pair (pair a b) refl))) = refl

inv-map-fib-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) (t : C × D) →
  (fib f (pr1 t)) × (fib g (pr2 t)) → fib (map-prod f g) t
pr1
  ( pr1
    ( inv-map-fib-map-prod f g (pair .(f x) .(g y))
      ( pair (pair x refl) (pair y refl)))) = x
pr2
  ( pr1
    ( inv-map-fib-map-prod f g (pair .(f x) .(g y))
      ( pair (pair x refl) (pair y refl)))) = y
pr2
  ( inv-map-fib-map-prod f g (pair .(f x) .(g y))
    ( pair (pair x refl) (pair y refl))) = refl

abstract
  issec-inv-map-fib-map-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) (t : C × D) →
    ((map-fib-map-prod f g t) ∘ (inv-map-fib-map-prod f g t)) ~ id
  issec-inv-map-fib-map-prod f g (pair .(f x) .(g y))
    (pair (pair x refl) (pair y refl)) = refl

abstract
  isretr-inv-map-fib-map-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) (t : C × D) →
    ((inv-map-fib-map-prod f g t) ∘ (map-fib-map-prod f g t)) ~ id
  isretr-inv-map-fib-map-prod f g .(map-prod f g (pair a b))
    (pair (pair a b) refl) = refl

abstract
  is-equiv-map-fib-map-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) (t : C × D) →
    is-equiv (map-fib-map-prod f g t)
  is-equiv-map-fib-map-prod f g t =
    is-equiv-has-inverse
      ( inv-map-fib-map-prod f g t)
      ( issec-inv-map-fib-map-prod f g t)
      ( isretr-inv-map-fib-map-prod f g t)

abstract
  is-equiv-left-factor-is-equiv-map-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) (d : D) →
    is-equiv (map-prod f g) → is-equiv f
  is-equiv-left-factor-is-equiv-map-prod f g d is-equiv-fg =
    is-equiv-is-contr-map
      ( λ x → is-contr-left-factor-prod
        ( fib f x)
        ( fib g d)
        ( is-contr-is-equiv'
          ( fib (map-prod f g) (pair x d))
          ( map-fib-map-prod f g (pair x d))
          ( is-equiv-map-fib-map-prod f g (pair x d))
          ( is-contr-map-is-equiv is-equiv-fg (pair x d))))

abstract
  is-equiv-right-factor-is-equiv-map-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) (c : C) →
    is-equiv (map-prod f g) → is-equiv g
  is-equiv-right-factor-is-equiv-map-prod f g c is-equiv-fg =
    is-equiv-is-contr-map
      ( λ y → is-contr-right-factor-prod
        ( fib f c)
        ( fib g y)
        ( is-contr-is-equiv'
          ( fib (map-prod f g) (pair c y))
          ( map-fib-map-prod f g (pair c y))
          ( is-equiv-map-fib-map-prod f g (pair c y))
          ( is-contr-map-is-equiv is-equiv-fg (pair c y))))

abstract
  is-pullback-left-factor-is-pullback-prod :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback
      ( map-prod f f')
      ( map-prod g g')
      ( cone-pair f g f' g' c c') →
    canonical-pullback f' g' → is-pullback f g c
  is-pullback-left-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t =
    is-equiv-left-factor-is-equiv-map-prod (gap f g c) (gap f' g' c') t
      ( is-equiv-right-factor
        ( gap
          ( map-prod f f')
          ( map-prod g g')
          ( cone-pair f g f' g' c c'))
      ( map-cone-pair f g f' g')
        ( map-prod (gap f g c) (gap f' g' c'))
        ( triangle-map-cone-pair f g c f' g' c')
        ( is-equiv-map-cone-pair f g f' g')
        ( is-pb-cc'))

abstract
  is-pullback-right-factor-is-pullback-prod :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback
      ( map-prod f f')
      ( map-prod g g')
      ( cone-pair f g f' g' c c') →
    canonical-pullback f g → is-pullback f' g' c'
  is-pullback-right-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t =
    is-equiv-right-factor-is-equiv-map-prod (gap f g c) (gap f' g' c') t
      ( is-equiv-right-factor
        ( gap
          ( map-prod f f')
          ( map-prod g g')
          ( cone-pair f g f' g' c c'))
        ( map-cone-pair f g f' g')
        ( map-prod (gap f g c) (gap f' g' c'))
        ( triangle-map-cone-pair f g c f' g' c')
        ( is-equiv-map-cone-pair f g f' g')
        ( is-pb-cc'))

-- Exercise 10.8

cone-Π :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i)) →
  cone (map-Π f) (map-Π g) ((i : I) → C i)
cone-Π f g c =
  triple
    ( map-Π (λ i → pr1 (c i)))
    ( map-Π (λ i → pr1 (pr2 (c i))))
    ( htpy-map-Π (λ i → pr2 (pr2 (c i))))

map-canonical-pullback-Π :
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
  canonical-pullback (map-Π f) (map-Π g) →
  (i : I) → canonical-pullback (f i) (g i)
map-canonical-pullback-Π f g (pair α (pair β γ)) i =
  triple (α i) (β i) (htpy-eq γ i)

inv-map-canonical-pullback-Π :
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
  ((i : I) → canonical-pullback (f i) (g i)) →
  canonical-pullback (map-Π f) (map-Π g)
inv-map-canonical-pullback-Π f g h =
  triple
    ( λ i → (pr1 (h i)))
    ( λ i → (pr1 (pr2 (h i))))
    ( eq-htpy (λ i → (pr2 (pr2 (h i)))))

abstract
  issec-inv-map-canonical-pullback-Π :
    {l1 l2 l3 l4 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
    ((map-canonical-pullback-Π f g) ∘ (inv-map-canonical-pullback-Π f g)) ~ id
  issec-inv-map-canonical-pullback-Π f g h =
    eq-htpy
      ( λ i → map-extensionality-canonical-pullback (f i) (g i) refl refl
        ( inv
          ( ( right-unit) ∙
            ( htpy-eq (issec-eq-htpy (λ i → (pr2 (pr2 (h i))))) i))))

abstract
  isretr-inv-map-canonical-pullback-Π :
    {l1 l2 l3 l4 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
    ((inv-map-canonical-pullback-Π f g) ∘ (map-canonical-pullback-Π f g)) ~ id
  isretr-inv-map-canonical-pullback-Π f g (pair α (pair β γ)) =
    map-extensionality-canonical-pullback
      ( map-Π f)
      ( map-Π g)
      refl
      refl
      ( inv (right-unit ∙ (isretr-eq-htpy γ)))

abstract
  is-equiv-map-canonical-pullback-Π :
    {l1 l2 l3 l4 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
    is-equiv (map-canonical-pullback-Π f g)
  is-equiv-map-canonical-pullback-Π f g =
    is-equiv-has-inverse
      ( inv-map-canonical-pullback-Π f g)
      ( issec-inv-map-canonical-pullback-Π f g)
      ( isretr-inv-map-canonical-pullback-Π f g)

triangle-map-canonical-pullback-Π :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i)) →
  ( map-Π (λ i → gap (f i) (g i) (c i))) ~
  ( ( map-canonical-pullback-Π f g) ∘
    ( gap (map-Π f) (map-Π g) (cone-Π f g c)))
triangle-map-canonical-pullback-Π f g c h =
  eq-htpy (λ i →
    map-extensionality-canonical-pullback
      (f i)
      (g i)
      refl refl
      ( (htpy-eq (issec-eq-htpy _) i) ∙ (inv right-unit)))

abstract
  is-pullback-cone-Π :
    {l1 l2 l3 l4 l5 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
    (c : (i : I) → cone (f i) (g i) (C i)) →
    ((i : I) → is-pullback (f i) (g i) (c i)) →
    is-pullback (map-Π f) (map-Π g) (cone-Π f g c)
  is-pullback-cone-Π f g c is-pb-c =
    is-equiv-right-factor
      ( map-Π (λ i → gap (f i) (g i) (c i)))
      ( map-canonical-pullback-Π f g)
      ( gap (map-Π f) (map-Π g) (cone-Π f g c))
      ( triangle-map-canonical-pullback-Π f g c)
      ( is-equiv-map-canonical-pullback-Π f g)
      ( is-equiv-map-Π _ is-pb-c)

-- Exercise 10.9

hom-cospan :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X') →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l1' ⊔ (l2' ⊔ l3')))))
hom-cospan {A = A} {B} {X} f g {A'} {B'} {X'} f' g' =
  Σ (A → A') (λ hA →
    Σ (B → B') (λ hB →
      Σ (X → X') (λ hX →
        ((f' ∘ hA) ~ (hX ∘ f)) × ((g' ∘ hB) ~ (hX ∘ g)))))

id-hom-cospan :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X) →
  hom-cospan f g f g
pr1 (id-hom-cospan f g) = id
pr1 (pr2 (id-hom-cospan f g)) = id
pr1 (pr2 (pr2 (id-hom-cospan f g))) = id
pr1 (pr2 (pr2 (pr2 (id-hom-cospan f g)))) = refl-htpy
pr2 (pr2 (pr2 (pr2 (id-hom-cospan f g)))) = refl-htpy

functor-canonical-pullback :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X') →
  hom-cospan f' g' f g →
  canonical-pullback f' g' → canonical-pullback f g
functor-canonical-pullback f g f' g'
  (pair hA (pair hB (pair hX (pair HA HB)))) (pair a' (pair b' p')) =
  triple (hA a') (hB b') ((HA a') ∙ ((ap hX p') ∙ (inv (HB b'))))

cospan-hom-cospan-rotate :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B'' → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  hom-cospan (pr1 h) (pr1 h') (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
pr1
  ( cospan-hom-cospan-rotate f g f' g' f'' g''
    ( pair hA (pair hB (pair hX (pair HA HB))))
    ( pair hA' (pair hB' (pair hX' (pair HA' HB'))))) = f'
pr1
  ( pr2
    ( cospan-hom-cospan-rotate f g f' g' f'' g''
      ( pair hA (pair hB (pair hX (pair HA HB))))
      ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))) = f''
pr1
  ( pr2
    ( pr2
      ( cospan-hom-cospan-rotate f g f' g' f'' g''
        ( pair hA (pair hB (pair hX (pair HA HB))))
        ( pair hA' (pair hB' (pair hX' (pair HA' HB'))))))) = f
pr1
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-rotate f g f' g' f'' g''
          ( pair hA (pair hB (pair hX (pair HA HB))))
          ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))))) = inv-htpy HA
pr2
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-rotate f g f' g' f'' g''
          ( pair hA (pair hB (pair hX (pair HA HB))))
          ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))))) = inv-htpy HA'

cospan-hom-cospan-rotate' :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B'' → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  hom-cospan
    (pr1 (pr2 h)) (pr1 (pr2 h')) (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
pr1
  ( cospan-hom-cospan-rotate' f g f' g' f'' g''
    ( pair hA (pair hB (pair hX (pair HA HB))))
    ( pair hA' (pair hB' (pair hX' (pair HA' HB'))))) = g'
pr1
  ( pr2
    ( cospan-hom-cospan-rotate' f g f' g' f'' g''
      ( pair hA (pair hB (pair hX (pair HA HB))))
      ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))) = g''
pr1
  ( pr2
    ( pr2
      ( cospan-hom-cospan-rotate' f g f' g' f'' g''
        ( pair hA (pair hB (pair hX (pair HA HB))))
        ( pair hA' (pair hB' (pair hX' (pair HA' HB'))))))) = g
pr1
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-rotate' f g f' g' f'' g''
          ( pair hA (pair hB (pair hX (pair HA HB))))
          ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))))) = inv-htpy HB
pr2
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-rotate' f g f' g' f'' g''
          ( pair hA (pair hB (pair hX (pair HA HB))))
          ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))))) = inv-htpy HB'

{-
map-3-by-3-canonical-pullback' :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  Σ ( canonical-pullback f' g') (λ t' →
    Σ ( canonical-pullback f'' g'') (λ t'' →
      Eq-canonical-pullback f g
        ( functor-canonical-pullback f g f' g' h t')
        ( functor-canonical-pullback f g f'' g'' h' t''))) →
  Σ ( canonical-pullback (pr1 h) (pr1 h')) (λ s →
    Σ ( canonical-pullback (pr1 (pr2 h)) (pr1 (pr2 h'))) (λ s' →
      Eq-canonical-pullback (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
        ( functor-canonical-pullback
          ( pr1 (pr2 (pr2 h)))
          ( pr1 (pr2 (pr2 h')))
          ( pr1 h)
          ( pr1 h')
          ( cospan-hom-cospan-rotate f g f' g' f'' g'' h h')
          ( s))
        ( functor-canonical-pullback
          ( pr1 (pr2 (pr2 h)))
          ( pr1 (pr2 (pr2 h')))
          ( pr1 (pr2 h))
          ( pr1 (pr2 h'))
          ( cospan-hom-cospan-rotate' f g f' g' f'' g'' h h')
          ( s'))))
map-3-by-3-canonical-pullback' f g f' g' f'' g''
  ( pair hA (pair hB (pair hX (pair HA HB))))
  ( pair hA' (pair hB' (pair hX' (pair HA' HB'))))
  ( pair
    ( pair a' (pair b' p'))
    ( pair (pair a'' (pair b'' p'')) (pair α (pair β γ)))) =
  pair (pair a' (pair a'' α)) (pair (pair b' (pair b'' β)) (pair p' (pair p'' {!!})))

map-3-by-3-canonical-pullback :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  canonical-pullback
    ( functor-canonical-pullback f g f' g' h)
    ( functor-canonical-pullback f g f'' g'' h') →
  canonical-pullback
    ( functor-canonical-pullback
      ( pr1 (pr2 (pr2 h)))
      ( pr1 (pr2 (pr2 h')))
      ( pr1 h)
      ( pr1 h')
      ( cospan-hom-cospan-rotate f g f' g' f'' g'' h h'))
    ( functor-canonical-pullback
      ( pr1 (pr2 (pr2 h)))
      ( pr1 (pr2 (pr2 h')))
      ( pr1 (pr2 h))
      ( pr1 (pr2 h'))
      ( cospan-hom-cospan-rotate' f g f' g' f'' g'' h h'))
map-3-by-3-canonical-pullback = {!!}
-}
```
