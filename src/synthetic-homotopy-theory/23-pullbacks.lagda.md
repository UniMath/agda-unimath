---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.23-pullbacks where

open import foundation.cartesian-product-types
open import foundation.commuting-squares
open import foundation.cones-pullbacks
open import foundation.constant-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.pullbacks
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-pullbacks
open import foundation.universe-levels

-- Section 13.1 Cartesian squares

-- Section 13.2

-- Section 13.3 Fiber products

-- Section 13.4 Fibers as pullbacks

-- Section 13.5 Fiberwise equivalences

-- Section 13.6 The pullback pasting property

-- Section 13.7 Descent for coproducts and Σ-types

-- Descent for Σ-types

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

-- Exercise 10.2

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
