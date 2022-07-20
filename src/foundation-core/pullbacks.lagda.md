---
title: Pullbacks
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.pullbacks where

open import foundation-core.commuting-squares
open import foundation-core.cones-pullbacks
open import foundation-core.dependent-pair-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.universal-property-pullbacks
open import foundation-core.universe-levels

open import foundation.identity-types
open import foundation.type-theoretic-principle-of-choice
```

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  canonical-pullback : UU ((l1 ⊔ l2) ⊔ l3)
  canonical-pullback = Σ A (λ x → Σ B (λ y → f x ＝ g y))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {f : A → X} {g : B → X}
  where
   
  π₁ : canonical-pullback f g → A
  π₁ = pr1

  π₂ : canonical-pullback f g → B
  π₂ t = pr1 (pr2 t)

  π₃ : (f ∘ π₁) ~ (g ∘ π₂)
  π₃ t = pr2 (pr2 t)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where
  
  cone-canonical-pullback : cone f g (canonical-pullback f g)
  pr1 cone-canonical-pullback = π₁
  pr1 (pr2 cone-canonical-pullback) = π₂
  pr2 (pr2 cone-canonical-pullback) = π₃
```

### The canonical pullback satisfies the universal property of pullbacks

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  abstract
    universal-property-pullback-canonical-pullback : 
      {l : Level} →
      universal-property-pullback l f g (cone-canonical-pullback f g)
    universal-property-pullback-canonical-pullback C =
      is-equiv-comp
        ( cone-map f g (cone-canonical-pullback f g))
        ( tot (λ p → map-distributive-Π-Σ))
        ( mapping-into-Σ)
        ( refl-htpy)
        ( is-equiv-mapping-into-Σ)
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ p → is-equiv-map-distributive-Π-Σ))
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) 
  where

  {- The gap map of a square is the map fron the vertex of the cone into the
     canonical pullback. -}

  gap : cone f g C → C → canonical-pullback f g
  pr1 (gap (pair p (pair q H)) z) = p z
  pr1 (pr2 (gap (pair p (pair q H)) z)) = q z
  pr2 (pr2 (gap (pair p (pair q H)) z)) = H z

  {- The proposition is-pullback is the assertion that the gap map is an 
     equivalence. Note that this proposition is small, whereas the universal 
     property is a large proposition. Of course, we will show below that the
     proposition is-pullback is equivalent to the universal property of
     pullbacks. -}

  is-pullback : cone f g C → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-pullback c = is-equiv (gap c)

  {- A cone is equal to the value of cone-map at its own gap map. -}

  htpy-cone-up-pullback-canonical-pullback :
    (c : cone f g C) →
    htpy-cone f g (cone-map f g (cone-canonical-pullback f g) (gap c)) c
  pr1 (htpy-cone-up-pullback-canonical-pullback c) = refl-htpy
  pr1 (pr2 (htpy-cone-up-pullback-canonical-pullback c)) = refl-htpy
  pr2 (pr2 (htpy-cone-up-pullback-canonical-pullback c)) = right-unit-htpy

  {- We show that the universal property of the pullback implies that the gap
     map is an equivalence. -}

  abstract
    is-pullback-universal-property-pullback :
      (c : cone f g C) →
      ({l : Level} → universal-property-pullback l f g c) → is-pullback c
    is-pullback-universal-property-pullback c up =
      is-equiv-up-pullback-up-pullback
        ( cone-canonical-pullback f g)
        ( c)
        ( gap c)
        ( htpy-cone-up-pullback-canonical-pullback c)
        ( universal-property-pullback-canonical-pullback f g)
        ( up)

  {- We show that the universal property follows from the assumption that the
     the gap map is an equivalence. -}

  abstract
    universal-property-pullback-is-pullback :
      (c : cone f g C) → is-pullback c →
      {l : Level} → universal-property-pullback l f g c
    universal-property-pullback-is-pullback c is-pullback-c =
      up-pullback-up-pullback-is-equiv
        ( cone-canonical-pullback f g)
        ( c)
        ( gap c)
        ( htpy-cone-up-pullback-canonical-pullback c)
        ( is-pullback-c)
        ( universal-property-pullback-canonical-pullback f g)
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3)
  where

  canonical-pullback-Σ : UU (l1 ⊔ l3)
  canonical-pullback-Σ = Σ A (λ x → Q (f x))
  
  cone-subst : cone f (pr1 {B = Q}) canonical-pullback-Σ
  pr1 cone-subst = pr1
  pr1 (pr2 cone-subst) = map-Σ-map-base f Q
  pr2 (pr2 cone-subst) = refl-htpy

  inv-gap-cone-subst : canonical-pullback f (pr1 {B = Q}) → canonical-pullback-Σ
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
```

### The pullback pasting property

```agda
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
```
