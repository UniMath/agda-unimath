---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.functoriality-dependent-pair-types where

open import foundation.contractible-maps using
  ( is-equiv-is-contr-map; is-contr-map-is-equiv; is-contr-map)
open import foundation.contractible-types using
  ( is-contr-is-equiv; is-contr-is-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; map-equiv; is-equiv-map-equiv;
    is-equiv-comp; is-equiv-right-factor; is-fiberwise-equiv;
    is-equiv-top-is-equiv-bottom-square; is-equiv-bottom-is-equiv-top-square)
open import foundation.fibers-of-maps using
  ( fib; map-equiv-total-fib; is-equiv-map-equiv-total-fib)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (refl; inv)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

# Functoriality of dependent pair types

In this file we construct
- The action on total spaces of a family of maps
- The map on total spaces induced by a map between the base types
- The functoriality of Σ-types

We compute the fibers of these maps and prove basic properties of them

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where

  {- Any family of maps induces a map on the total spaces. -}
  
  tot : Σ A B → Σ A C
  pr1 (tot t) = pr1 t
  pr2 (tot t) = f (pr1 t) (pr2 t)

  {- We show that for any family of maps, the fiber of the induced map on total
     spaces are equivalent to the fibers of the maps in the family. -}
   
  map-compute-fib-tot : (t : Σ A C) → fib tot t → fib (f (pr1 t)) (pr2 t)
  pr1 (map-compute-fib-tot .(tot (pair x y)) (pair (pair x y) refl)) = y
  pr2 (map-compute-fib-tot .(tot (pair x y)) (pair (pair x y) refl)) = refl

  map-inv-compute-fib-tot : (t : Σ A C) → fib (f (pr1 t)) (pr2 t) → fib tot t
  pr1 (pr1 (map-inv-compute-fib-tot (pair a .(f a y)) (pair y refl))) = a
  pr2 (pr1 (map-inv-compute-fib-tot (pair a .(f a y)) (pair y refl))) = y
  pr2 (map-inv-compute-fib-tot (pair a .(f a y)) (pair y refl)) = refl

  issec-map-inv-compute-fib-tot :
    (t : Σ A C) → (map-compute-fib-tot t ∘ map-inv-compute-fib-tot t) ~ id
  issec-map-inv-compute-fib-tot (pair x .(f x y)) (pair y refl) = refl

  isretr-map-inv-compute-fib-tot :
    (t : Σ A C) → (map-inv-compute-fib-tot t ∘ map-compute-fib-tot t) ~ id
  isretr-map-inv-compute-fib-tot .(pair x (f x y)) (pair (pair x y) refl) = refl

  abstract
    is-equiv-map-compute-fib-tot :
      (t : Σ A C) → is-equiv (map-compute-fib-tot t)
    is-equiv-map-compute-fib-tot t =
      is-equiv-has-inverse
        ( map-inv-compute-fib-tot t)
        ( issec-map-inv-compute-fib-tot t)
        ( isretr-map-inv-compute-fib-tot t)

  compute-fib-tot : (t : Σ A C) → fib tot t ≃ fib (f (pr1 t)) (pr2 t)
  pr1 (compute-fib-tot t) = map-compute-fib-tot t
  pr2 (compute-fib-tot t) = is-equiv-map-compute-fib-tot t

  abstract
    is-equiv-map-inv-compute-fib-tot :
      (t : Σ A C) → is-equiv (map-inv-compute-fib-tot t)
    is-equiv-map-inv-compute-fib-tot t =
      is-equiv-has-inverse
        ( map-compute-fib-tot t)
        ( isretr-map-inv-compute-fib-tot t)
        ( issec-map-inv-compute-fib-tot t)

  inv-compute-fib-tot : (t : Σ A C) → fib (f (pr1 t)) (pr2 t) ≃ fib tot t
  pr1 (inv-compute-fib-tot t) = map-inv-compute-fib-tot t
  pr2 (inv-compute-fib-tot t) = is-equiv-map-inv-compute-fib-tot t

tot-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H (pair x y) = eq-pair-Σ refl (H x y)

tot-id :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  (tot (λ x (y : B x) → y)) ~ id
tot-id B (pair x y) = refl

tot-comp :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2} {B' : A → UU l3} {B'' : A → UU l4}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → (g x) ∘ (f x)) ~ ((tot g) ∘ (tot f))
tot-comp f g (pair x y) = refl

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-equiv-tot-is-fiberwise-equiv : is-fiberwise-equiv f → is-equiv (tot f )
    is-equiv-tot-is-fiberwise-equiv H =
      is-equiv-is-contr-map
        ( λ t →
          is-contr-is-equiv
            ( fib (f (pr1 t)) (pr2 t))
            ( map-compute-fib-tot f t)
            ( is-equiv-map-compute-fib-tot f t)
            ( is-contr-map-is-equiv (H (pr1 t)) (pr2 t)))

  abstract
    is-fiberwise-equiv-is-equiv-tot : is-equiv (tot f) → is-fiberwise-equiv f
    is-fiberwise-equiv-is-equiv-tot is-equiv-tot-f x =
      is-equiv-is-contr-map
        ( λ z →
          is-contr-is-equiv'
            ( fib (tot f) (pair x z))
            ( map-compute-fib-tot f (pair x z))
            ( is-equiv-map-compute-fib-tot f (pair x z))
            ( is-contr-map-is-equiv is-equiv-tot-f (pair x z)))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  equiv-tot : ((x : A) → B x ≃ C x) → (Σ A B) ≃ (Σ A C)
  pr1 (equiv-tot e) = tot (λ x → map-equiv (e x))
  pr2 (equiv-tot e) =
    is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-map-equiv (e x))

{- In the second part of this section we show that any equivalence f on base 
   types also induces an equivalence on total spaces. -}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  map-Σ-map-base : Σ A (λ x → C (f x)) → Σ B C
  pr1 (map-Σ-map-base s) = f (pr1 s)
  pr2 (map-Σ-map-base s) = pr2 s

  {- The proof is similar to the previous part: we show that the fibers of f
     and Σ-kap-base-map f C are equivalent. -}

  fib-map-Σ-map-base-fib :
    (t : Σ B C) → fib f (pr1 t) → fib map-Σ-map-base t
  pr1 (pr1 (fib-map-Σ-map-base-fib (pair .(f x) z) (pair x refl))) = x
  pr2 (pr1 (fib-map-Σ-map-base-fib (pair .(f x) z) (pair x refl))) = z
  pr2 (fib-map-Σ-map-base-fib (pair .(f x) z) (pair x refl)) = refl

  fib-fib-map-Σ-map-base :
    (t : Σ B C) → fib map-Σ-map-base t → fib f (pr1 t)
  pr1
    ( fib-fib-map-Σ-map-base
      .(map-Σ-map-base (pair x z)) (pair (pair x z) refl)) = x
  pr2
    ( fib-fib-map-Σ-map-base
      .(map-Σ-map-base (pair x z)) (pair (pair x z) refl)) = refl
  
  issec-fib-fib-map-Σ-map-base :
    (t : Σ B C) → (fib-map-Σ-map-base-fib t ∘ fib-fib-map-Σ-map-base t) ~ id
  issec-fib-fib-map-Σ-map-base .(pair (f x) z) (pair (pair x z) refl) = refl

  isretr-fib-fib-map-Σ-map-base :
    (t : Σ B C) → (fib-fib-map-Σ-map-base t ∘ fib-map-Σ-map-base-fib t) ~ id
  isretr-fib-fib-map-Σ-map-base (pair .(f x) z) (pair x refl) = refl

  abstract
    is-equiv-fib-map-Σ-map-base-fib :
      (t : Σ B C) → is-equiv (fib-map-Σ-map-base-fib t)
    is-equiv-fib-map-Σ-map-base-fib t =
      is-equiv-has-inverse
        ( fib-fib-map-Σ-map-base t)
        ( issec-fib-fib-map-Σ-map-base t)
        ( isretr-fib-fib-map-Σ-map-base t)

  equiv-fib-map-Σ-map-base-fib :
    (t : Σ B C) → fib f (pr1 t) ≃ fib map-Σ-map-base t
  pr1 (equiv-fib-map-Σ-map-base-fib t) = fib-map-Σ-map-base-fib t
  pr2 (equiv-fib-map-Σ-map-base-fib t) = is-equiv-fib-map-Σ-map-base-fib t

  abstract
    is-contr-map-map-Σ-map-base : is-contr-map f → is-contr-map map-Σ-map-base
    is-contr-map-map-Σ-map-base is-contr-f (pair y z) =
      is-contr-is-equiv'
        ( fib f y)
        ( fib-map-Σ-map-base-fib (pair y z))
        ( is-equiv-fib-map-Σ-map-base-fib (pair y z))
        ( is-contr-f y)

  abstract
    is-equiv-map-Σ-map-base : is-equiv f → is-equiv map-Σ-map-base
    is-equiv-map-Σ-map-base is-equiv-f =
      is-equiv-is-contr-map
        ( is-contr-map-map-Σ-map-base (is-contr-map-is-equiv is-equiv-f))

equiv-Σ-equiv-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (e : A ≃ B) →
  Σ A (C ∘ (map-equiv e)) ≃ Σ B C
pr1 (equiv-Σ-equiv-base C (pair f is-equiv-f)) = map-Σ-map-base f C
pr2 (equiv-Σ-equiv-base C (pair f is-equiv-f)) =
  is-equiv-map-Σ-map-base f C is-equiv-f

{- Now we combine the two parts of this section. -}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4)
  where
  
  map-Σ :
    (f : A → B) (g : (x : A) → C x → D (f x)) → Σ A C → Σ B D
  pr1 (map-Σ f g t) = f (pr1 t)
  pr2 (map-Σ f g t) = g (pr1 t) (pr2 t)

  triangle-map-Σ :
    (f : A → B) (g : (x : A) → C x → D (f x)) →
    (map-Σ f g) ~ (map-Σ-map-base f D ∘ tot g)
  triangle-map-Σ f g t = refl

  abstract
    is-equiv-map-Σ :
      (f : A → B) (g : (x : A) → C x → D (f x)) →
      is-equiv f → is-fiberwise-equiv g → is-equiv (map-Σ f g)
    is-equiv-map-Σ f g is-equiv-f is-fiberwise-equiv-g =
      is-equiv-comp
        ( map-Σ f g)
        ( map-Σ-map-base f D)
        ( tot g)
        ( triangle-map-Σ f g)
        ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-g)
        ( is-equiv-map-Σ-map-base f D is-equiv-f)

  equiv-Σ :
    (e : A ≃ B) (g : (x : A) → C x ≃ D (map-equiv e x)) → Σ A C ≃ Σ B D
  pr1 (equiv-Σ e g) = map-Σ (map-equiv e) (λ x → map-equiv (g x))
  pr2 (equiv-Σ e g) =
    is-equiv-map-Σ
      ( map-equiv e)
      ( λ x → map-equiv (g x))
      ( is-equiv-map-equiv e)
      ( λ x → is-equiv-map-equiv (g x))

  abstract
    is-fiberwise-equiv-is-equiv-map-Σ :
      (f : A → B) (g : (x : A) → C x → D (f x)) →
      is-equiv f → is-equiv (map-Σ f g) → is-fiberwise-equiv g
    is-fiberwise-equiv-is-equiv-map-Σ f g H K =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-right-factor
          ( map-Σ f g)
          ( map-Σ-map-base f D)
          ( tot g)
          ( triangle-map-Σ f g)
          ( is-equiv-map-Σ-map-base f D H)
          ( K))
```

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where
  
  fib-triangle :
    (x : X) → (fib f x) → (fib g x)
  pr1 (fib-triangle .(f a) (pair a refl)) = h a
  pr2 (fib-triangle .(f a) (pair a refl)) = inv (H a)

  square-tot-fib-triangle :
    (h ∘ (map-equiv-total-fib f)) ~ (map-equiv-total-fib g ∘ tot fib-triangle)
  square-tot-fib-triangle (pair .(f a) (pair a refl)) = refl

  abstract
    is-fiberwise-equiv-is-equiv-triangle :
      (E : is-equiv h) → is-fiberwise-equiv fib-triangle
    is-fiberwise-equiv-is-equiv-triangle E =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-is-equiv-bottom-square
          ( map-equiv-total-fib f)
          ( map-equiv-total-fib g)
          ( tot fib-triangle)
          ( h)
          ( square-tot-fib-triangle)
          ( is-equiv-map-equiv-total-fib f)
          ( is-equiv-map-equiv-total-fib g)
          ( E))

  abstract
    is-equiv-triangle-is-fiberwise-equiv :
      is-fiberwise-equiv fib-triangle → is-equiv h
    is-equiv-triangle-is-fiberwise-equiv E =
      is-equiv-bottom-is-equiv-top-square
        ( map-equiv-total-fib f)
        ( map-equiv-total-fib g)
        ( tot fib-triangle)
        ( h)
        ( square-tot-fib-triangle)
        ( is-equiv-map-equiv-total-fib f)
        ( is-equiv-map-equiv-total-fib g)
        ( is-equiv-tot-is-fiberwise-equiv E)
```
