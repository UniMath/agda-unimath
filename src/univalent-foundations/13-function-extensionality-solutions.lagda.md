---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-foundations.13-function-extensionality-solutions where

open import foundation public
open import elementary-number-theory public

-- Exercise 13.5

-- Exercise 13.11

isretr-section-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (sec-h : sec h) →
  ((section-comp f g h H sec-h) ∘ (section-comp' f g h H sec-h)) ~ id
isretr-section-comp f g h H (pair k K) (pair l L) =
  eq-htpy-sec
    ( ( section-comp f g h H (pair k K) ∘
        section-comp' f g h H (pair k K))
      ( pair l L))
    ( pair l L)
    ( K ·r l)
    ( ( inv-htpy
        ( assoc-htpy
          ( inv-htpy (H ·r (k ∘ l)))
          ( H ·r (k ∘ l))
          ( (g ·l (K ·r l)) ∙h L))) ∙h
      ( ap-concat-htpy'
        ( (inv-htpy (H ·r (k ∘ l))) ∙h (H ·r (k ∘ l)))
        ( refl-htpy)
        ( (g ·l (K ·r l)) ∙h L)
        ( left-inv-htpy (H ·r (k ∘ l)))))

sec-left-factor-retract-of-sec-composition :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → (sec g) retract-of (sec f)
pr1 (sec-left-factor-retract-of-sec-composition {X = X} f g h H sec-h) =
  section-comp' f g h H sec-h
pr1 (pr2 (sec-left-factor-retract-of-sec-composition {X = X} f g h H sec-h)) =
  section-comp f g h H sec-h
pr2 (pr2 (sec-left-factor-retract-of-sec-composition {X = X} f g h H sec-h)) =
  isretr-section-comp f g h H sec-h

isretr-retraction-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (retr-g : retr g) →
  ((retraction-comp f g h H retr-g) ∘ (retraction-comp' f g h H retr-g)) ~ id
isretr-retraction-comp f g h H (pair l L) (pair k K) =
  eq-htpy-retr
    ( ( retraction-comp f g h H (pair l L)
        ( retraction-comp' f g h H (pair l L)
          ( pair k K))))
    ( pair k K)
    ( k ·l L)
    ( ( inv-htpy
        ( assoc-htpy
          ( inv-htpy ((k ∘ l) ·l H))
          ( (k ∘ l) ·l H)
          ( (k ·l (L ·r h)) ∙h K))) ∙h
      ( ap-concat-htpy'
        ( (inv-htpy ((k ∘ l) ·l H)) ∙h ((k ∘ l) ·l H))
        ( refl-htpy)
        ( (k ·l (L ·r h)) ∙h K)
        ( left-inv-htpy ((k ∘ l) ·l H))))
  
sec-right-factor-retract-of-sec-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → (retr h) retract-of (retr f)
pr1 (sec-right-factor-retract-of-sec-left-factor f g h H retr-g) =
  retraction-comp' f g h H retr-g
pr1 (pr2 (sec-right-factor-retract-of-sec-left-factor f g h H retr-g)) =
  retraction-comp f g h H retr-g
pr2 (pr2 (sec-right-factor-retract-of-sec-left-factor f g h H retr-g)) =
  isretr-retraction-comp f g h H retr-g

-- Exercise 13.12

-- Distributitivty of Π over coproducts

is-prop-is-zero-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-prop (is-zero-Fin x)
is-prop-is-zero-Fin {k} x = is-set-Fin (succ-ℕ k) x zero-Fin

is-prop-is-one-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-prop (is-one-Fin x)
is-prop-is-one-Fin {k} x = is-set-Fin (succ-ℕ k) x one-Fin

is-prop-is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → is-prop (coprod (is-zero-Fin x) (is-one-Fin x))
is-prop-is-zero-or-one-Fin-two-ℕ x =
  is-prop-coprod
    ( λ p q → Eq-Fin-eq (inv p ∙ q))
    ( is-prop-is-zero-Fin x)
    ( is-prop-is-one-Fin x)

is-contr-is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → is-contr (coprod (is-zero-Fin x) (is-one-Fin x))
is-contr-is-zero-or-one-Fin-two-ℕ x =
  is-proof-irrelevant-is-prop
    ( is-prop-is-zero-or-one-Fin-two-ℕ x)
    ( is-zero-or-one-Fin-two-ℕ x)

-- We express coproducts as Σ-types over Fin 2

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
  
  fam-coprod :
    Fin 2  → UU (l1 ⊔ l2)
  fam-coprod (inl (inr star)) = raise l2 A
  fam-coprod (inr star) = raise l1 B
  
  map-compute-total-fam-coprod :
    Σ (Fin 2) fam-coprod → coprod A B
  map-compute-total-fam-coprod (pair (inl (inr star)) y) = inl (map-inv-raise y)
  map-compute-total-fam-coprod (pair (inr star) y) = inr (map-inv-raise y)

  map-inv-compute-total-fam-coprod :
    coprod A B → Σ (Fin 2) fam-coprod
  pr1 (map-inv-compute-total-fam-coprod (inl x)) = zero-Fin
  pr2 (map-inv-compute-total-fam-coprod (inl x)) = map-raise x
  pr1 (map-inv-compute-total-fam-coprod (inr x)) = one-Fin
  pr2 (map-inv-compute-total-fam-coprod (inr x)) = map-raise x

  issec-map-inv-compute-total-fam-coprod :
    (map-compute-total-fam-coprod ∘ map-inv-compute-total-fam-coprod) ~ id
  issec-map-inv-compute-total-fam-coprod (inl x) =
    ap inl (isretr-map-inv-raise {l2} x)
  issec-map-inv-compute-total-fam-coprod (inr x) =
    ap inr (isretr-map-inv-raise {l1} x)

  isretr-map-inv-compute-total-fam-coprod :
    (map-inv-compute-total-fam-coprod ∘ map-compute-total-fam-coprod) ~ id
  isretr-map-inv-compute-total-fam-coprod (pair (inl (inr star)) y) =
    ap (pair zero-Fin) (issec-map-inv-raise y)
  isretr-map-inv-compute-total-fam-coprod (pair (inr star) y) =
    ap (pair one-Fin) (issec-map-inv-raise y)

  is-equiv-map-compute-total-fam-coprod :
    is-equiv map-compute-total-fam-coprod
  is-equiv-map-compute-total-fam-coprod =
    is-equiv-has-inverse
      map-inv-compute-total-fam-coprod
      issec-map-inv-compute-total-fam-coprod
      isretr-map-inv-compute-total-fam-coprod
  
  compute-total-fam-coprod :
    (Σ (Fin 2) fam-coprod) ≃ coprod A B
  pr1 compute-total-fam-coprod = map-compute-total-fam-coprod
  pr2 compute-total-fam-coprod = is-equiv-map-compute-total-fam-coprod

  inv-compute-total-fam-coprod :
    coprod A B ≃ Σ (Fin 2) fam-coprod
  inv-compute-total-fam-coprod =
    inv-equiv compute-total-fam-coprod
  
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3}
  where

  type-distributive-Π-coprod : UU (l1 ⊔ l2 ⊔ l3)
  type-distributive-Π-coprod =
    Σ ( X → Fin 2)
      ( λ f → ((x : X) (p : is-zero-Fin (f x)) → A x) ×
              ((x : X) (p : is-one-Fin (f x)) → B x))

  distributive-Π-coprod :
    ((x : X) → coprod (A x) (B x)) ≃ type-distributive-Π-coprod
  distributive-Π-coprod =
    ( ( equiv-tot
        ( λ f →
          ( ( equiv-prod
              ( equiv-map-Π
                ( λ x →
                  equiv-map-Π
                    ( λ p →
                      ( inv-equiv (equiv-raise l3 (A x))) ∘e
                      ( equiv-tr (fam-coprod (A x) (B x)) p))))
              ( equiv-map-Π
                ( λ x →
                  equiv-map-Π
                    ( λ p →
                      ( inv-equiv (equiv-raise l2 (B x))) ∘e
                      ( equiv-tr (fam-coprod (A x) (B x)) p))))) ∘e
            ( distributive-Π-Σ)) ∘e
          ( equiv-map-Π
            ( λ x →
              ( equiv-universal-property-coprod
                ( fam-coprod (A x) (B x) (f x))) ∘e
              ( equiv-diagonal-is-contr
                ( fam-coprod (A x) (B x) (f x))
                ( is-contr-is-zero-or-one-Fin-two-ℕ (f x))))))) ∘e
      ( distributive-Π-Σ)) ∘e
    ( equiv-map-Π
      ( λ x → inv-compute-total-fam-coprod (A x) (B x)))

{- Getting rid of fib in a Π-type -}

map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((y : B) (z : fib f y) → C y z) → ((x : A) → C (f x) (pair x refl))
map-reduce-Π-fib f C h x = h (f x) (pair x refl)

inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((x : A) → C (f x) (pair x refl)) → ((y : B) (z : fib f y) → C y z)
inv-map-reduce-Π-fib f C h .(f x) (pair x refl) = h x

issec-inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((map-reduce-Π-fib f C) ∘ (inv-map-reduce-Π-fib f C)) ~ id
issec-inv-map-reduce-Π-fib f C h = refl

isretr-inv-map-reduce-Π-fib' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  (h : (y : B) (z : fib f y) → C y z) (y : B) →
  (inv-map-reduce-Π-fib f C ((map-reduce-Π-fib f C) h) y) ~ (h y)
isretr-inv-map-reduce-Π-fib' f C h .(f z) (pair z refl) = refl

isretr-inv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fib f y) → UU l3) →
  ((inv-map-reduce-Π-fib f C) ∘ (map-reduce-Π-fib f C)) ~ id
isretr-inv-map-reduce-Π-fib f C h =
  eq-htpy (λ y → eq-htpy (isretr-inv-map-reduce-Π-fib' f C h y))

is-equiv-map-reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : (y : B) (z : fib f y) → UU l3) →
  is-equiv (map-reduce-Π-fib f C)
is-equiv-map-reduce-Π-fib f C =
  is-equiv-has-inverse
    ( inv-map-reduce-Π-fib f C)
    ( issec-inv-map-reduce-Π-fib f C)
    ( isretr-inv-map-reduce-Π-fib f C)

reduce-Π-fib' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : (y : B) (z : fib f y) → UU l3) →
  ((y : B) (z : fib f y) → C y z) ≃ ((x : A) → C (f x) (pair x refl))
pr1 (reduce-Π-fib' f C) = map-reduce-Π-fib f C
pr2 (reduce-Π-fib' f C) = is-equiv-map-reduce-Π-fib f C

reduce-Π-fib :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : B → UU l3) → ((y : B) → fib f y → C y) ≃ ((x : A) → C (f x))
reduce-Π-fib f C = reduce-Π-fib' f (λ y z → C y)

-- Exercise 13.16

{- We relate morphisms in the slice category to fiberwise morphisms -}
  
fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  hom-slice f g → (x : X) → (fib f x) → (fib g x)
fiberwise-hom-hom-slice f g (pair h H) = fib-triangle f g h H

hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((x : X) → (fib f x) → (fib g x)) → hom-slice f g
pr1 (hom-slice-fiberwise-hom f g α) a = pr1 (α (f a) (pair a refl))
pr2 (hom-slice-fiberwise-hom f g α) a = inv (pr2 (α (f a) (pair a refl)))

issec-hom-slice-fiberwise-hom-eq-htpy :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (α : (x : X) → (fib f x) → (fib g x)) (x : X) →
  (fiberwise-hom-hom-slice f g (hom-slice-fiberwise-hom f g α) x) ~ (α x)
issec-hom-slice-fiberwise-hom-eq-htpy f g α .(f a) (pair a refl) =
  eq-pair-Σ refl (inv-inv (pr2 (α (f a) (pair a refl))))

issec-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((fiberwise-hom-hom-slice f g) ∘ (hom-slice-fiberwise-hom f g)) ~ id
issec-hom-slice-fiberwise-hom f g α =
  eq-htpy (λ x → eq-htpy (issec-hom-slice-fiberwise-hom-eq-htpy f g α x))

isretr-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((hom-slice-fiberwise-hom f g) ∘ (fiberwise-hom-hom-slice f g)) ~ id
isretr-hom-slice-fiberwise-hom f g (pair h H) =
  eq-pair-Σ refl (eq-htpy (λ a → (inv-inv (H a))))

abstract
  is-equiv-fiberwise-hom-hom-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (fiberwise-hom-hom-slice f g)
  is-equiv-fiberwise-hom-hom-slice f g =
    is-equiv-has-inverse
      ( hom-slice-fiberwise-hom f g)
      ( issec-hom-slice-fiberwise-hom f g)
      ( isretr-hom-slice-fiberwise-hom f g)

equiv-fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  hom-slice f g ≃ ((x : X) → fib f x → fib g x)
pr1 (equiv-fiberwise-hom-hom-slice f g) = fiberwise-hom-hom-slice f g
pr2 (equiv-fiberwise-hom-hom-slice f g) = is-equiv-fiberwise-hom-hom-slice f g

abstract
  is-equiv-hom-slice-fiberwise-hom :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (hom-slice-fiberwise-hom f g)
  is-equiv-hom-slice-fiberwise-hom f g =
    is-equiv-has-inverse
      ( fiberwise-hom-hom-slice f g)
      ( isretr-hom-slice-fiberwise-hom f g)
      ( issec-hom-slice-fiberwise-hom f g)

equiv-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((x : X) → fib f x → fib g x) ≃ hom-slice f g
pr1 (equiv-hom-slice-fiberwise-hom f g) = hom-slice-fiberwise-hom f g
pr2 (equiv-hom-slice-fiberwise-hom f g) = is-equiv-hom-slice-fiberwise-hom f g

equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
equiv-slice {A = A} {B} f g = Σ (A ≃ B) (λ e → f ~ (g ∘ (map-equiv e)))

hom-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g → hom-slice f g
pr1 (hom-equiv-slice f g e) = pr1 (pr1 e)
pr2 (hom-equiv-slice f g e) = pr2 e

{- We first prove two closely related generic lemmas that establishes 
   equivalences of subtypes -}

abstract
  is-equiv-subtype-is-equiv :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    is-equiv f → ((x : A) → (Q (f x)) → P x) → is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv {Q = Q} is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-map-Σ Q f g is-equiv-f
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x)) (h x))

abstract
  is-equiv-subtype-is-equiv' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    (is-equiv-f : is-equiv f) →
    ((y : B) → (Q y) → P (map-inv-is-equiv is-equiv-f y)) →
    is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv' {P = P} {Q}
    is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-map-Σ Q f g is-equiv-f
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x))
        ( (tr P (isretr-map-inv-is-equiv is-equiv-f x)) ∘ (h (f x))))

abstract
  is-fiberwise-equiv-fiberwise-equiv-equiv-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X)
    (t : hom-slice f g) → is-equiv (pr1 t) →
    is-fiberwise-equiv (fiberwise-hom-hom-slice f g t)
  is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g (pair h H) =
    is-fiberwise-equiv-is-equiv-triangle f g h H

abstract
  is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    (t : hom-slice f g) →
    ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
    is-equiv (pr1 t)
  is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
    f g (pair h H) =
    is-equiv-triangle-is-fiberwise-equiv f g h H

equiv-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g ≃ Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
equiv-fiberwise-equiv-equiv-slice f g =
  equiv-Σ is-fiberwise-equiv (equiv-fiberwise-hom-hom-slice f g) α ∘e
  equiv-right-swap-Σ
  where
  α   : ( h : hom-slice f g) →
        is-equiv (pr1 h) ≃
        is-fiberwise-equiv (map-equiv (equiv-fiberwise-hom-hom-slice f g) h)
  α h = equiv-prop
          ( is-subtype-is-equiv _)
          ( is-prop-Π (λ x → is-subtype-is-equiv _))
          ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g h)
          ( is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
            f g h)

fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g → Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
fiberwise-equiv-equiv-slice f g =
  map-equiv (equiv-fiberwise-equiv-equiv-slice f g)
    
equiv-fam-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g ≃ ((x : X) → (fib f x) ≃ (fib g x))
equiv-fam-equiv-equiv-slice f g =
  ( inv-distributive-Π-Σ) ∘e
  ( equiv-fiberwise-equiv-equiv-slice f g)

-- Exercise 13.17

hom-over-morphism :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) → UU (l1 ⊔ (l2 ⊔ l4))
hom-over-morphism i f g = hom-slice (i ∘ f) g

fiberwise-hom-hom-over-morphism :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  hom-over-morphism i f g → (x : X) → (fib f x) → (fib g (i x))
pr1 (fiberwise-hom-hom-over-morphism i f g (pair h H) .(f a) (pair a refl)) =
  h a
pr2 (fiberwise-hom-hom-over-morphism i f g (pair h H) .(f a) (pair a refl)) =
  inv (H a)

hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  ((x : X) → (fib f x) → (fib g (i x))) → hom-over-morphism i f g
pr1 (hom-over-morphism-fiberwise-hom i f g α) a = pr1 (α (f a) (pair a refl))
pr2 (hom-over-morphism-fiberwise-hom i f g α) a =
  inv (pr2 (α (f a) (pair a refl)))

issec-hom-over-morphism-fiberwise-hom-eq-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  (α : (x : X) → (fib f x) → (fib g (i x))) (x : X) →
  ( fiberwise-hom-hom-over-morphism i f g
    ( hom-over-morphism-fiberwise-hom i f g α) x) ~ (α x)
issec-hom-over-morphism-fiberwise-hom-eq-htpy i f g α .(f a) (pair a refl) =
  eq-pair-Σ refl (inv-inv (pr2 (α (f a) (pair a refl))))

issec-hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  ( ( fiberwise-hom-hom-over-morphism i f g) ∘
    ( hom-over-morphism-fiberwise-hom i f g)) ~ id
issec-hom-over-morphism-fiberwise-hom i f g α =
  eq-htpy
    ( λ x →
      ( eq-htpy
        ( issec-hom-over-morphism-fiberwise-hom-eq-htpy i f g α x)))

isretr-hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  ( ( hom-over-morphism-fiberwise-hom i f g) ∘
    ( fiberwise-hom-hom-over-morphism i f g)) ~ id
isretr-hom-over-morphism-fiberwise-hom i f g (pair h H) =
  eq-pair-Σ refl (eq-htpy (λ a → (inv-inv (H a))))

abstract
  is-equiv-fiberwise-hom-hom-over-morphism :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    (i : X → Y) (f : A → X) (g : B → Y) →
    is-equiv (fiberwise-hom-hom-over-morphism i f g)
  is-equiv-fiberwise-hom-hom-over-morphism i f g =
    is-equiv-has-inverse
      ( hom-over-morphism-fiberwise-hom i f g)
      ( issec-hom-over-morphism-fiberwise-hom i f g)
      ( isretr-hom-over-morphism-fiberwise-hom i f g)

abstract
  is-equiv-hom-over-morphism-fiberwise-hom :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    (i : X → Y) (f : A → X) (g : B → Y) →
    is-equiv (hom-over-morphism-fiberwise-hom i f g)
  is-equiv-hom-over-morphism-fiberwise-hom i f g =
    is-equiv-has-inverse
      ( fiberwise-hom-hom-over-morphism i f g)
      ( isretr-hom-over-morphism-fiberwise-hom i f g)
      ( issec-hom-over-morphism-fiberwise-hom i f g)

-- Exercise 13.18

module _
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2)
  where

  is-iso-Set : (f : type-hom-Set A B) → UU (l1 ⊔ l2)
  is-iso-Set f = Σ (type-hom-Set B A) (λ g → (Id (f ∘ g) id) × (Id (g ∘ f) id))

  iso-Set : UU (l1 ⊔ l2)
  iso-Set = Σ (type-hom-Set A B) is-iso-Set

  map-iso-Set : iso-Set → type-Set A → type-Set B
  map-iso-Set = pr1

  is-iso-map-iso-Set : (f : iso-Set) → is-iso-Set (map-iso-Set f)
  is-iso-map-iso-Set = pr2

  is-proof-irrelevant-is-iso-Set :
    (f : type-hom-Set A B) → is-proof-irrelevant (is-iso-Set f)
  pr1 (is-proof-irrelevant-is-iso-Set f H) = H
  pr2
    ( is-proof-irrelevant-is-iso-Set f
      ( pair g (pair p q)))
      ( pair g' (pair p' q')) =
    eq-subtype
      ( λ h →
        prod-Prop
          ( Id-Prop (hom-Set B B) (f ∘ h) id)
          ( Id-Prop (hom-Set A A) (h ∘ f) id))
      ( ( ap (λ h → g ∘ h) (inv p')) ∙
        ( ap (λ h → h ∘ g') q))

  is-prop-is-iso-Set : (f : type-hom-Set A B) → is-prop (is-iso-Set f)
  is-prop-is-iso-Set f =
    is-prop-is-proof-irrelevant (is-proof-irrelevant-is-iso-Set f)

  is-iso-is-equiv-Set : {f : type-hom-Set A B} → is-equiv f → is-iso-Set f
  pr1 (is-iso-is-equiv-Set H) = map-inv-is-equiv H
  pr1 (pr2 (is-iso-is-equiv-Set H)) = eq-htpy (issec-map-inv-is-equiv H)
  pr2 (pr2 (is-iso-is-equiv-Set H)) = eq-htpy (isretr-map-inv-is-equiv H)

  is-equiv-is-iso-Set : {f : type-hom-Set A B} → is-iso-Set f → is-equiv f
  is-equiv-is-iso-Set H =
    is-equiv-has-inverse
      ( pr1 H)
      ( htpy-eq (pr1 (pr2 H)))
      ( htpy-eq (pr2 (pr2 H)))

  iso-equiv-Set : type-equiv-Set A B → iso-Set
  pr1 (iso-equiv-Set e) = map-equiv e
  pr2 (iso-equiv-Set e) = is-iso-is-equiv-Set (is-equiv-map-equiv e)

  equiv-iso-Set : iso-Set → type-equiv-Set A B
  pr1 (equiv-iso-Set f) = map-iso-Set f
  pr2 (equiv-iso-Set f) = is-equiv-is-iso-Set (is-iso-map-iso-Set f)

  equiv-iso-equiv-Set : type-equiv-Set A B ≃ iso-Set
  equiv-iso-equiv-Set =
    equiv-type-subtype
      ( is-subtype-is-equiv)
      ( is-prop-is-iso-Set)
      ( λ f → is-iso-is-equiv-Set)
      ( λ f → is-equiv-is-iso-Set)

-- Exercise 13.19

-- Exercise 13.20

-- Exercise 13.21

-- Exercise 13.15

cases-function-converse-weak-funext :
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} (d : has-decidable-equality I)
  (H : is-contr ((i : I) → A i)) (i : I) (x : A i)
  (j : I) (e : is-decidable (Id i j)) → A j
cases-function-converse-weak-funext d H i x .i (inl refl) = x
cases-function-converse-weak-funext d H i x j (inr f) = center H j

function-converse-weak-funext :
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} (d : has-decidable-equality I)
  (H : is-contr ((i : I) → A i)) (i : I) (x : A i) (j : I) → A j
function-converse-weak-funext d H i x j =
  cases-function-converse-weak-funext d H i x j (d i j)

cases-eq-function-converse-weak-funext :
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} (d : has-decidable-equality I)
  (H : is-contr ((i : I) → A i)) (i : I) (x : A i) (e : is-decidable (Id i i)) →
  Id (cases-function-converse-weak-funext d H i x i e) x
cases-eq-function-converse-weak-funext d H i x (inl p) =
  ap ( λ t → cases-function-converse-weak-funext d H i x i (inl t))
     ( eq-is-prop (is-set-has-decidable-equality d i i) {p} {refl})
cases-eq-function-converse-weak-funext d H i x (inr f) = ex-falso (f refl)

eq-function-converse-weak-funext :
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} (d : has-decidable-equality I)
  (H : is-contr ((i : I) → A i)) (i : I) (x : A i) →
  Id (function-converse-weak-funext d H i x i) x
eq-function-converse-weak-funext d H i x =
  cases-eq-function-converse-weak-funext d H i x (d i i)

converse-weak-funext :
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} →
  has-decidable-equality I → is-contr ((i : I) → A i) → (i : I) → is-contr (A i)
pr1 (converse-weak-funext d (pair x H) i) = x i
pr2 (converse-weak-funext d (pair x H) i) y =
  ( htpy-eq (H (function-converse-weak-funext d (pair x H) i y)) i) ∙
  ( eq-function-converse-weak-funext d (pair x H) i y)

--------------------------------------------------------------------------------

{- Some lemmas about equivalences on Π-types -}

abstract
  is-equiv-inv-con-htpy :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
    ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
    is-equiv (inv-con-htpy H K L)
  is-equiv-inv-con-htpy H K L =
    is-equiv-map-Π _ (λ x → is-equiv-inv-con (H x) (K x) (L x))

equiv-inv-con-htpy :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
  ( (H ∙h K) ~ L) ≃ (K ~ ((inv-htpy H) ∙h L))
pr1 (equiv-inv-con-htpy H K L) = inv-con-htpy H K L
pr2 (equiv-inv-con-htpy H K L) = is-equiv-inv-con-htpy H K L

abstract
  is-equiv-con-inv-htpy :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
    ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
    is-equiv (con-inv-htpy H K L)
  is-equiv-con-inv-htpy H K L =
    is-equiv-map-Π _ (λ x → is-equiv-con-inv (H x) (K x) (L x))

equiv-con-inv-htpy :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
  ( (H ∙h K) ~ L) ≃ (H ~ (L ∙h (inv-htpy K)))
pr1 (equiv-con-inv-htpy H K L) = con-inv-htpy H K L
pr2 (equiv-con-inv-htpy H K L) = is-equiv-con-inv-htpy H K L

HTPY-map-equiv-Π :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} (B' : A' → UU l2) {A : UU l3} (B : A → UU l4)
  ( e e' : A' ≃ A) (H : htpy-equiv e e') →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
HTPY-map-equiv-Π {A' = A'} B' {A} B e e' H =
  ( f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
  ( f' : (a' : A') → B' a' ≃ B (map-equiv e' a')) →
  ( K : (a' : A') →
        ((tr B (H a')) ∘ (map-equiv (f a'))) ~ (map-equiv (f' a'))) →
  ( map-equiv-Π B e f) ~ (map-equiv-Π B e' f')

htpy-map-equiv-Π-refl-htpy :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) →
  HTPY-map-equiv-Π B' B e e (refl-htpy-equiv e)
htpy-map-equiv-Π-refl-htpy {B' = B'} B e f f' K =
  ( htpy-map-Π
    ( λ a →
      ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a)) ·l
      ( K (map-inv-is-equiv (is-equiv-map-equiv e) a)))) ·r
  ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')

abstract
  htpy-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e e' : A' ≃ A) (H : htpy-equiv e e') →
    HTPY-map-equiv-Π B' B e e' H
  htpy-map-equiv-Π {B' = B'} B e e' H f f' K =
    ind-htpy-equiv e
      ( HTPY-map-equiv-Π B' B e)
      ( htpy-map-equiv-Π-refl-htpy B e)
      e' H f f' K
  
  comp-htpy-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e : A' ≃ A) →
    Id ( htpy-map-equiv-Π {B' = B'} B e e (refl-htpy-equiv e))
      ( ( htpy-map-equiv-Π-refl-htpy B e))
  comp-htpy-map-equiv-Π {B' = B'} B e =
    comp-htpy-equiv e
      ( HTPY-map-equiv-Π B' B e)
      ( htpy-map-equiv-Π-refl-htpy B e)

map-automorphism-Π :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
  ( (a : A) → B a) → ((a : A) → B a)
map-automorphism-Π {B = B} e f =
  ( map-Π (λ a → (map-inv-is-equiv (is-equiv-map-equiv (f a))))) ∘
  ( precomp-Π (map-equiv e) B)

abstract
  is-equiv-map-automorphism-Π :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
    is-equiv (map-automorphism-Π e f)
  is-equiv-map-automorphism-Π {B = B} e f =
    is-equiv-comp' _ _
      ( is-equiv-precomp-Π-is-equiv _ (is-equiv-map-equiv e) B)
      ( is-equiv-map-Π _
        ( λ a → is-equiv-map-inv-is-equiv (is-equiv-map-equiv (f a))))

automorphism-Π :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
  ( (a : A) → B a) ≃ ((a : A) → B a)
pr1 (automorphism-Π e f) = map-automorphism-Π e f
pr2 (automorphism-Π e f) = is-equiv-map-automorphism-Π e f

--------------------------------------------------------------------------------

function-Fin :
  (k l : ℕ) → (Fin k → Fin l) ≃ Fin (exp-ℕ l k)
function-Fin zero-ℕ l =
  ( inv-left-unit-law-coprod unit) ∘e
  ( equiv-is-contr (universal-property-empty' (Fin l)) is-contr-unit)
function-Fin (succ-ℕ k) l =
  ( ( prod-Fin (exp-ℕ l k) l) ∘e
    ( equiv-prod (function-Fin k l) (equiv-universal-property-unit (Fin l)))) ∘e
  ( equiv-universal-property-coprod (Fin l))

--------------------------------------------------------------------------------

{-
pointed-successor-algebra : {l : Level} (X : UU l) → UU l
pointed-successor-algebra X = X × (X → X)

pointed-successor-algebra-ℕ : pointed-successor-algebra ℕ
pointed-successor-algebra-ℕ = pair zero-ℕ succ-ℕ

Eq-pointed-successor-algebra :
  {l : Level} {X : UU l} (x y : pointed-successor-algebra X) → UU l
Eq-pointed-successor-algebra x y =
  (Id (pr1 x) (pr1 y)) × ((pr2 x) ~ (pr2 y))

refl-Eq-pointed-successor-algebra :
  {l : Level} {X : UU l} (x : pointed-successor-algebra X) →
  Eq-pointed-successor-algebra x x
refl-Eq-pointed-successor-algebra (pair x f) = pair refl refl-htpy

Eq-pointed-successor-algebra-eq :
  {l : Level} {X : UU l} (x y : pointed-successor-algebra X) →
  Id x y → Eq-pointed-successor-algebra x y
Eq-pointed-successor-algebra-eq x .x refl =
  refl-Eq-pointed-successor-algebra x

is-contr-total-Eq-pointed-successor-algebra :
  {l : Level} {X : UU l} (x : pointed-successor-algebra X) →
  is-contr (Σ (pointed-successor-algebra X) (Eq-pointed-successor-algebra x))
is-contr-total-Eq-pointed-successor-algebra {l} {X} x =
  is-contr-total-Eq-structure
    ( λ (y : X) (g : X → X) (p : Id (pr1 x) y) → (pr2 x) ~ g)
    ( is-contr-total-path (pr1 x))
    ( pair (pr1 x) refl)
    ( is-contr-total-htpy (pr2 x))

ev-zero-succ-ℕ :
  {l : Level} {X : UU l} → pointed-successor-algebra X → ℕ → X
ev-zero-succ-ℕ (pair x f) zero-ℕ = x
ev-zero-succ-ℕ (pair x f) (succ-ℕ n) = f (ev-zero-succ-ℕ (pair x f) n)

hom-pointed-successor-algebra :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (H : pointed-successor-algebra X) (K : pointed-successor-algebra Y) →
  UU (l1 ⊔ l2)
hom-pointed-successor-algebra {l1} {l2} {X} {Y} H K =
  Σ ( X → Y)
    ( λ h →
      ( Id (h (pr1 H)) (pr1 K)) ×
      ( (x : X) → Id (h (pr2 H x)) (pr2 K (h x))))

map-hom-pointed-successor-algebra :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (H : pointed-successor-algebra X) (K : pointed-successor-algebra Y) →
  (h : hom-pointed-successor-algebra H K) → X → Y
map-hom-pointed-successor-algebra H K h = pr1 h

comp-base-hom-pointed-successor-algebra :
  {l1 l2 : Level} {X : UU l1} {Y : UU l1}
  (H : pointed-successor-algebra X) (K : pointed-successor-algebra Y) →
  (h : hom-pointed-successor-algebra H K) →
  Id (map-hom-pointed-successor-algebra H K h (pr1 H)) (pr1 K)
comp-base-hom-pointed-successor-algebra H K h =
  pr1 (pr2 h)

comp-succ-hom-pointed-successor-algebra :
  {l1 l2 : Level} {X : UU l1} {Y : UU l1}
  (H : pointed-successor-algebra X) (K : pointed-successor-algebra Y) →
  (h : hom-pointed-successor-algebra H K) →
  (map-hom-pointed-successor-algebra H K h ∘ (pr2 H)) ~
  (pr2 K ∘ (map-hom-pointed-successor-algebra H K h))
comp-succ-hom-pointed-successor-algebra H K h =
  pr2 (pr2 h)

hom-is-initial-pointed-successor-algebra-ℕ :
  {l1 : Level} {X : UU l1} (x : pointed-successor-algebra X) →
  hom-pointed-successor-algebra pointed-successor-algebra-ℕ x
hom-is-initial-pointed-successor-algebra-ℕ x =
  pair
    ( ind-ℕ (pr1 x) (λ n → (pr2 x)))
    ( pair refl refl-htpy)

htpy-hom-pointed-successor-algebra :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (H : pointed-successor-algebra X) (K : pointed-successor-algebra Y) →
  (h1 h2 : hom-pointed-successor-algebra H K) → UU (l1 ⊔ l2)
htpy-hom-pointed-successor-algebra H K h1 h2 =
  Σ ( (pr1 h1) ~ pr1 h2)
    ( λ α →
      {! Id (comp-base-hom-pointed-successor-algebra H K h1) ? × ?!})

-}

--------------------------------------------------------------------------------
```
