---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --allow-unsolved-metas --exact-split #-}

module synthetic-homotopy-theory.25-cubical-diagrams where

open import foundation.commuting-cubes
open import foundation.commuting-squares
open import foundation.cones-pullbacks
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-pullbacks
open import foundation.universe-levels

open import synthetic-homotopy-theory.24-pushouts

descent-is-equiv :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  (c : cone j h B) (d : cone i (pr1 c) A) →
  is-equiv i → is-equiv (pr1 (pr2 d)) →
  is-pullback (j ∘ i) h (cone-comp-horizontal i j h c d) →
  is-pullback j h c
descent-is-equiv i j h c d
  is-equiv-i is-equiv-k is-pb-rectangle =
  is-pullback-is-fiberwise-equiv-map-fib-cone j h c
    ( map-inv-is-equiv-precomp-Π-is-equiv
      ( i)
      ( is-equiv-i)
      ( λ y → is-equiv (map-fib-cone j h c y))
      ( λ x → is-equiv-left-factor
        ( map-fib-cone (j ∘ i) h
          ( cone-comp-horizontal i j h c d) x)
        ( map-fib-cone j h c (i x))
        ( map-fib-cone i (pr1 c) d x)
        ( map-fib-cone-comp-horizontal i j h c d x)
        ( is-fiberwise-equiv-map-fib-cone-is-pullback (j ∘ i) h
          ( cone-comp-horizontal i j h c d)
          ( is-pb-rectangle)
          ( x))
        ( is-fiberwise-equiv-map-fib-cone-is-pullback i (pr1 c) d
          ( is-pullback-is-equiv' i (pr1 c) d is-equiv-i is-equiv-k) x)))

coherence-htpy-square-is-pullback-bottom-is-pullback-top-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  coherence-htpy-parallel-cone
    ( front-left)
    ( refl-htpy' k)
    ( pair f'
      ( pair
        ( g ∘ hA)
        ( rectangle-back-left-bottom-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
    ( pair f'
      ( pair
        ( hC ∘ g')
        ( rectangle-top-front-right-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
    ( refl-htpy' f')
    ( back-right)
coherence-htpy-square-is-pullback-bottom-is-pullback-top-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c =
  ( inv-htpy
    ( inv-htpy
      ( assoc-htpy
        ( h ·l (inv-htpy back-left))
        ( bottom ·r hA)
        ( (k ·l back-right) ∙h (refl-htpy' (k ∘ (hC ∘ g'))))))) ∙h
  ( ( ap-concat-htpy'
      ( h ·l (inv-htpy back-left))
      ( inv-htpy (h ·l back-left))
      ( _)
      ( left-whisk-inv-htpy h back-left)) ∙h
      ( inv-htpy (inv-con-htpy (h ·l back-left) _ _
        ( ( ( inv-htpy (assoc-htpy (h ·l back-left) (front-left ·r f') _)) ∙h
            ( ( inv-htpy
                ( assoc-htpy
                  ( (h ·l back-left) ∙h (front-left ·r f'))
                  ( hD ·l top)
                  ( (inv-htpy front-right) ·r g'))) ∙h
              inv-htpy
              ( con-inv-htpy _ (front-right ·r g') _
                ( (assoc-htpy (bottom ·r hA) _ _) ∙h (inv-htpy (c)))))) ∙h
          ( inv-htpy
            ( ap-concat-htpy (bottom ·r hA) _ _ right-unit-htpy))))))

is-pullback-bottom-is-pullback-top-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
  is-pullback h' k' (pair f' (pair g' top)) →
  is-pullback h k (pair f (pair g bottom))
is-pullback-bottom-is-pullback-top-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-top =
  descent-is-equiv hB h k
    ( pair f (pair g bottom))
    ( pair f' (pair hA (inv-htpy (back-left))))
    ( is-equiv-hB)
    ( is-equiv-hA)
    ( is-pullback-htpy
      {f = h ∘ hB}
      -- ( hD ∘ h')
      ( front-left)
      {g = k}
      -- ( k)
      ( refl-htpy' k)
      { c = pair f'
        ( pair
          ( g ∘ hA)
          ( rectangle-back-left-bottom-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))}
       ( pair
        ( f')
        ( pair
          ( hC ∘ g')
          ( rectangle-top-front-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom)))
      ( pair
        ( refl-htpy' f')
        ( pair
          ( back-right)
          ( coherence-htpy-square-is-pullback-bottom-is-pullback-top-cube-is-equiv
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c)))
      ( is-pullback-rectangle-is-pullback-left-square
        ( h')
        ( hD)
        ( k)
        ( pair k' (pair hC (inv-htpy front-right)))
        ( pair f' (pair g' top))
        ( is-pullback-is-equiv' hD k
          ( pair k' (pair hC (inv-htpy front-right)))
          ( is-equiv-hD)
          ( is-equiv-hC))
        ( is-pb-top)))

is-pullback-top-is-pullback-bottom-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
  is-pullback h k (pair f (pair g bottom)) →
  is-pullback h' k' (pair f' (pair g' top))
is-pullback-top-is-pullback-bottom-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-bottom =
  is-pullback-top-is-pullback-rectangle h hD k'
    ( pair hB (pair h' front-left))
    ( pair f' (pair g' top))
    ( is-pullback-is-equiv h hD
      ( pair hB (pair h' front-left))
      is-equiv-hD is-equiv-hB)
    ( is-pullback-htpy' refl-htpy front-right
      ( cone-comp-vertical h k hC
        ( pair f (pair g bottom))
        ( pair hA (pair g' back-right)))
      { c' = cone-comp-vertical h hD k'
        ( pair hB (pair h' front-left))
        ( pair f' (pair g' top))}
      ( pair back-left
        ( pair
          ( refl-htpy)
          ( ( ( ( assoc-htpy
                    ( bottom ·r hA) (k ·l back-right) (front-right ·r g')) ∙h
                ( inv-htpy c)) ∙h
              ( assoc-htpy
                  ( h ·l back-left) (front-left ·r f') (hD ·l top))) ∙h
            ( ap-concat-htpy'
              ( h ·l back-left)
              ( (h ·l back-left) ∙h refl-htpy)
              ( (front-left ·r f') ∙h (hD ·l top))
              ( inv-htpy right-unit-htpy)))))
      ( is-pullback-rectangle-is-pullback-top h k hC
        ( pair f (pair g bottom))
        ( pair hA (pair g' back-right))
        ( is-pb-bottom)
        ( is-pullback-is-equiv g hC
          ( pair hA (pair g' back-right))
          is-equiv-hC is-equiv-hA)))

is-pullback-front-left-is-pullback-back-right-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  is-equiv f' → is-equiv f → is-equiv k' → is-equiv k →
  is-pullback g hC (pair hA (pair g' back-right)) →
  is-pullback h hD (pair hB (pair h' front-left))
is-pullback-front-left-is-pullback-back-right-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right =
  is-pullback-bottom-is-pullback-top-cube-is-equiv
    hB h' h hD hA g' g hC f' f k' k
    back-right (inv-htpy back-left) top bottom (inv-htpy front-right) front-left
    ( coherence-cube-mirror-B f g h k f' g' h' k' hA hB hC hD top
      back-left back-right front-left front-right bottom c)
    is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right

is-pullback-front-right-is-pullback-back-left-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  is-equiv g' → is-equiv h' → is-equiv g → is-equiv h →
  is-pullback f hB (pair hA (pair f' back-left)) →
  is-pullback k hD (pair hC (pair k' front-right))
is-pullback-front-right-is-pullback-back-left-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-g' is-equiv-h' is-equiv-g is-equiv-h is-pb-back-left =
  is-pullback-bottom-is-pullback-top-cube-is-equiv
    hC k' k hD hA f' f hB g' g h' h
    back-left (inv-htpy back-right) (inv-htpy top)
    ( inv-htpy bottom) (inv-htpy front-left) front-right
    ( coherence-cube-rotate-120 f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom c)
    is-equiv-g' is-equiv-g is-equiv-h' is-equiv-h is-pb-back-left

-- Section 15.2 Fiberwise pullbacks.

{- We show that if we have a square of families, such that the base square is
   a pullback square, then each square of fibers is a pullback square if and
   only if the square of total spaces is a pullback square. -}

cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  cone f g C → (C → UU l8) → UU (l4 ⊔ (l5 ⊔ (l6 ⊔ (l7 ⊔ l8))))
cone-family {C = C} PX f' g' c PC =
  (x : C) →
  cone ((tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x))) (g' (pr1 (pr2 c) x)) (PC x)

htpy-map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3} (Q : B → UU l4)
  {f f' : A → B} (H : f ~ f') (g : (x : A) → P x → Q (f x)) {g' : (x : A) → P x → Q (f' x)} (K : (x : A) → ((tr Q (H x)) ∘ (g x)) ~ (g' x)) →
  (map-Σ Q f g) ~ (map-Σ Q f' g')
htpy-map-Σ Q H g K t = eq-pair-Σ (H (pr1 t)) (K (pr1 t) (pr2 t))

tot-cone-cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) → cone-family PX f' g' c PC →
  cone (map-Σ PX f f') (map-Σ PX g g') (Σ C PC)
tot-cone-cone-family PX f' g' c c' =
  pair
    ( map-Σ _ (pr1 c) (λ x → pr1 (c' x)))
    ( pair
      ( map-Σ _ (pr1 (pr2 c)) (λ x → (pr1 (pr2 (c' x)))))
      ( htpy-map-Σ PX
        ( pr2 (pr2 c))
        ( λ z → (f' (pr1 c z)) ∘ (pr1 (c' z)))
        ( λ z → pr2 (pr2 (c' z)))))

map-canpb-tot-cone-cone-fam-right-factor :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  Σ ( canonical-pullback f g)
    ( λ t → canonical-pullback ((tr PX (π₃ t)) ∘ (f' (π₁ t))) (g' (π₂ t))) →
  Σ ( Σ A PA)
    ( λ aa' → Σ (Σ B (λ b → Id (f (pr1 aa')) (g b)))
      ( λ bα → Σ (PB (pr1 bα))
        ( λ b' → Id
          ( tr PX (pr2 bα) (f' (pr1 aa') (pr2 aa')))
          ( g' (pr1 bα) b'))))
map-canpb-tot-cone-cone-fam-right-factor
  {X = X} {A} {B} {C} PX {PA} {PB} {PC} {f} {g} f' g' c c' =
  map-interchange-Σ-Σ
    ( λ a bα a' → Σ (PB (pr1 bα))
      ( λ b' → Id (tr PX (pr2 bα) (f' a a')) (g' (pr1 bα) b')))

map-canpb-tot-cone-cone-fam-left-factor :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) → (aa' : Σ A PA) →
  Σ (Σ B (λ b → Id (f (pr1 aa')) (g b)))
    ( λ bα → Σ (PB (pr1 bα))
      ( λ b' → Id
        ( tr PX (pr2 bα) (f' (pr1 aa') (pr2 aa')))
        ( g' (pr1 bα) b'))) →
  Σ ( Σ B PB)
    ( λ bb' → Σ (Id (f (pr1 aa')) (g (pr1 bb')))
      ( λ α → Id (tr PX α (f' (pr1 aa') (pr2 aa'))) (g' (pr1 bb') (pr2 bb'))))
map-canpb-tot-cone-cone-fam-left-factor
  {X = X} {A} {B} {C} PX {PA} {PB} {PC} {f} {g} f' g' c c' aa' =
  ( map-interchange-Σ-Σ
    ( λ b α b' → Id (tr PX α (f' (pr1 aa') (pr2 aa'))) (g' b b')))

map-canonical-pullback-tot-cone-cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  Σ ( canonical-pullback f g)
    ( λ t → canonical-pullback ((tr PX (π₃ t)) ∘ (f' (π₁ t))) (g' (π₂ t))) →
  canonical-pullback (map-Σ PX f f') (map-Σ PX g g')
map-canonical-pullback-tot-cone-cone-family
  {X = X} {A} {B} {C} PX {PA} {PB} {PC} {f} {g} f' g' c c' =
  ( tot (λ aa' →
    ( tot (λ bb' → eq-pair-Σ')) ∘
    ( map-canpb-tot-cone-cone-fam-left-factor PX f' g' c c' aa'))) ∘
  ( map-canpb-tot-cone-cone-fam-right-factor PX f' g' c c')
  
is-equiv-map-canonical-pullback-tot-cone-cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  is-equiv (map-canonical-pullback-tot-cone-cone-family PX f' g' c c')
is-equiv-map-canonical-pullback-tot-cone-cone-family
  {X = X} {A} {B} {C} PX {PA} {PB} {PC} {f} {g} f' g' c c' =
  is-equiv-comp
    ( map-canonical-pullback-tot-cone-cone-family PX f' g' c c')
    ( tot (λ aa' →
      ( tot (λ bb' → eq-pair-Σ')) ∘
      ( map-canpb-tot-cone-cone-fam-left-factor PX f' g' c c' aa')))
    ( map-canpb-tot-cone-cone-fam-right-factor PX f' g' c c')
    ( refl-htpy)
    ( is-equiv-map-interchange-Σ-Σ
      ( λ a bα a' → Σ (PB (pr1 bα))
        ( λ b' → Id (tr PX (pr2 bα) (f' a a')) (g' (pr1 bα) b'))))
    ( is-equiv-tot-is-fiberwise-equiv (λ aa' → is-equiv-comp
      ( ( tot (λ bb' → eq-pair-Σ')) ∘
        ( map-canpb-tot-cone-cone-fam-left-factor PX f' g' c c' aa'))
      ( tot (λ bb' → eq-pair-Σ'))
      ( map-canpb-tot-cone-cone-fam-left-factor PX f' g' c c' aa')
      ( refl-htpy)
      ( is-equiv-map-interchange-Σ-Σ _)
      ( is-equiv-tot-is-fiberwise-equiv (λ bb' → is-equiv-eq-pair-Σ
        ( pair (f (pr1 aa')) (f' (pr1 aa') (pr2 aa')))
        ( pair (g (pr1 bb')) (g' (pr1 bb') (pr2 bb')))))))

triangle-canonical-pullback-tot-cone-cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  ( gap (map-Σ PX f f') (map-Σ PX g g') (tot-cone-cone-family PX f' g' c c')) ~
  ( ( map-canonical-pullback-tot-cone-cone-family PX f' g' c c') ∘
    ( map-Σ _
      ( gap f g c)
      ( λ x → gap
        ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
        ( g' (pr1 (pr2 c) x))
        ( c' x))))
triangle-canonical-pullback-tot-cone-cone-family PX f' g' c c' (pair x y) =
  refl

is-pullback-family-is-pullback-tot :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  is-pullback f g c →
  is-pullback
    (map-Σ PX f f') (map-Σ PX g g') (tot-cone-cone-family PX f' g' c c') →
  (x : C) →
  is-pullback
    ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
    ( g' (pr1 (pr2 c) x))
    ( c' x)
is-pullback-family-is-pullback-tot
  PX {PA} {PB} {PC} {f} {g} f' g' c c' is-pb-c is-pb-tot =
  is-fiberwise-equiv-is-equiv-map-Σ _
    ( gap f g c)
    ( λ x → gap
      ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
      ( g' (pr1 (pr2 c) x))
      ( c' x))
    ( is-pb-c)
    ( is-equiv-right-factor
      ( gap (map-Σ PX f f') (map-Σ PX g g') (tot-cone-cone-family PX f' g' c c'))
      ( map-canonical-pullback-tot-cone-cone-family PX f' g' c c')
      ( map-Σ _
        ( gap f g c)
        ( λ x → gap
          ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
          ( g' (pr1 (pr2 c) x))
          ( c' x)))
      ( triangle-canonical-pullback-tot-cone-cone-family PX f' g' c c')
      ( is-equiv-map-canonical-pullback-tot-cone-cone-family PX f' g' c c')
      ( is-pb-tot)) 

is-pullback-tot-is-pullback-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  is-pullback f g c →
  ( (x : C) →
    is-pullback
      ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
      ( g' (pr1 (pr2 c) x))
      ( c' x)) →
  is-pullback
    (map-Σ PX f f') (map-Σ PX g g') (tot-cone-cone-family PX f' g' c c')
is-pullback-tot-is-pullback-family
  PX {PA} {PB} {PC} {f} {g} f' g' c c' is-pb-c is-pb-c' =
  is-equiv-comp
    ( gap (map-Σ PX f f') (map-Σ PX g g') (tot-cone-cone-family PX f' g' c c'))
    ( map-canonical-pullback-tot-cone-cone-family PX f' g' c c')
    ( map-Σ _
      ( gap f g c)
      ( λ x → gap
        ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
        ( g' (pr1 (pr2 c) x))
        ( c' x)))
    ( triangle-canonical-pullback-tot-cone-cone-family PX f' g' c c')
    ( is-equiv-map-Σ _
      ( gap f g c)
      ( λ x → gap
        ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
        ( g' (pr1 (pr2 c) x))
        ( c' x))
        ( is-pb-c)
        ( is-pb-c'))
    ( is-equiv-map-canonical-pullback-tot-cone-cone-family PX f' g' c c')

{- We show that identity types commute with pullbacks. -}

cone-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (c1 c2 : C) →
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  cone
    ( λ (α : Id (p c1) (p c2)) → (ap f α) ∙ (H c2))
    ( λ (β : Id (q c1) (q c2)) → (H c1) ∙ (ap g β))
    ( Id c1 c2)
cone-ap f g (pair p (pair q H)) c1 c2 =
  pair
    ( ap p)
    ( pair
      ( ap q)
      ( λ γ →
        ( ap (λ t → t ∙ (H c2)) (inv (ap-comp f p γ))) ∙
        ( ( inv (nat-htpy H γ)) ∙
          ( ap (λ t → (H c1) ∙ t) (ap-comp g q γ)))))

tr-id-right :
  {l1 : Level} {A : UU l1} {a b c : A} (q : Id b c) (p : Id a b) →
  Id (tr (λ y → Id a y) q p) (p ∙ q)
tr-id-right refl refl = refl

cone-ap' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (c1 c2 : C) →
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  cone
    ( λ (α : Id (p c1) (p c2)) → tr (λ t → Id (f (p c1)) t) (H c2) (ap f α))
    ( λ (β : Id (q c1) (q c2)) → (H c1) ∙ (ap g β))
    ( Id c1 c2)
cone-ap' f g (pair p (pair q H)) c1 c2 =
  pair
    ( ap p)
    ( pair
      ( ap q)
      ( λ γ →
        ( tr-id-right (H c2) (ap f (ap p γ))) ∙
        ( ( ap (λ t → t ∙ (H c2)) (inv (ap-comp f p γ))) ∙
          ( ( inv (nat-htpy H γ)) ∙
            ( ap (λ t → (H c1) ∙ t) (ap-comp g q γ))))))

is-pullback-cone-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
  (c1 c2 : C) →
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  is-pullback
    ( λ (α : Id (p c1) (p c2)) → (ap f α) ∙ (H c2))
    ( λ (β : Id (q c1) (q c2)) → (H c1) ∙ (ap g β))
    ( cone-ap f g c c1 c2)
is-pullback-cone-ap f g (pair p (pair q H)) is-pb-c c1 c2 =
  is-pullback-htpy'
    -- ( λ α → tr (λ x → Id (f (p c1)) x) (H c2) (ap f α))
    ( λ α → tr-id-right (H c2) (ap f α))
    -- ( λ β → (H c1) ∙ (ap g β))
    ( refl-htpy)
    ( cone-ap' f g (pair p (pair q H)) c1 c2)
    { c' = cone-ap f g (pair p (pair q H)) c1 c2}
    ( pair refl-htpy (pair refl-htpy right-unit-htpy))
    ( is-pullback-family-is-pullback-tot
      ( λ x → Id (f (p c1)) x)
      ( λ a → ap f {x = p c1} {y = a})
      ( λ b β → (H c1) ∙ (ap g β))
      ( pair p (pair q H))
      ( cone-ap' f g (pair p (pair q H)) c1)
      ( is-pb-c)
      ( is-pullback-is-equiv
        ( map-Σ _ f (λ a α → ap f α))
        ( map-Σ _ g (λ b β → (H c1) ∙ (ap g β)))
        ( tot-cone-cone-family
          ( Id (f (p c1)))
          ( λ a → ap f)
          ( λ b β → (H c1) ∙ (ap g β))
          ( pair p (pair q H))
          ( cone-ap' f g (pair p (pair q H)) c1))
        ( is-equiv-is-contr _
          ( is-contr-total-path (q c1))
          ( is-contr-total-path (f (p c1))))
        ( is-equiv-is-contr _
          ( is-contr-total-path c1)
          ( is-contr-total-path (p c1))))
      ( c2))

{- Next we show that for any commuting cube, if the bottom and top squares are
   pullback squares, then so is the square of fibers of the vertical maps in
   cube. -}

{-

square-fib-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  (a : A) →
  ( ( tot (λ d' p → p ∙ (bottom a)) ∘
      ( map-fib-cone h hD (pair hB (pair h' front-left)) (f a))) ∘
    ( map-fib-cone f hB (pair hA (pair f' back-left)) a)) ~
  ( ( map-fib-cone k hD (pair hC (pair k' front-right)) (g a)) ∘
    ( map-fib-cone g hC (pair hA (pair g' back-right)) a))
square-fib-cube f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  .(hA a') (pair a' refl) =
  eq-pair-Σ
    ( pair
      ( top a')
      ( ( tr-id-left-subst
          ( top a')
          ( k (g (hA a')))
          ( ( ( inv (front-left (f' a'))) ∙
              ( ap h ((inv (back-left a')) ∙ refl))) ∙
            ( bottom (hA a')))) ∙
        ( ( ( assoc (inv (ap hD (top a'))) _ (bottom (hA a'))) ∙
            {!!}) ∙
          ( distributive-inv-concat (ap k (back-right a')) (front-right (g' a')) ∙
            ( ( ap
                ( concat (inv (front-right (g' a'))) ?)
                ( inv (ap-inv k (back-right a')))) ∙
              ( ap
                ( concat (inv (front-right (g' a'))) ?)
                ( ap (ap k) (inv right-unit))))))))
-}
```
