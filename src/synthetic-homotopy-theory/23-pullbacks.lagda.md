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

-- Exercises

-- Exercise 10.1

-- Exercise 10.2

-- Exercise 10.3

-- Exercise 10.4

-- Exercise 10.5

{- We show that a square is a pullback square if and only if every exponent of 
  it is a pullback square. -}

-- Exercise 10.6

{- Note: the solution below involves a substantial amount of path algebra. It
   would be nice to find a simpler solution.
   -}

-- Exercise 10.7

prod-cone :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  cone f g C → cone f' g' C' →
  cone (map-prod f f') (map-prod g g') (C × C')
pr1 (prod-cone f g f' g' (p , q , H) (p' , q' , H')) = map-prod p p'
pr1 (pr2 (prod-cone f g f' g' (p , q , H) (p' , q' , H'))) = map-prod q q'
pr2 (pr2 (prod-cone f g f' g' (p , q , H) (p' , q' , H'))) =
  ( inv-htpy (map-prod-comp p p' f f')) ∙h
  ( ( htpy-map-prod H H') ∙h
    ( map-prod-comp q q' g g'))

map-prod-cone :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  (canonical-pullback f g) × (canonical-pullback f' g') →
  canonical-pullback (map-prod f f') (map-prod g g')
map-prod-cone {A' = A'} {B'} f g f' g' =
  ( tot
    ( λ t →
      ( tot (λ s → eq-pair')) ∘
      ( map-interchange-Σ-Σ (λ y p y' → Id (f' (pr2 t)) (g' y'))))) ∘
  ( map-interchange-Σ-Σ (λ x t x' → Σ _ (λ y' → Id (f' x') (g' y'))))

triangle-map-prod-cone :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (c : cone f g C)
  (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
  (gap (map-prod f f') (map-prod g g') (prod-cone f g f' g' c c')) ~
  ((map-prod-cone f g f' g') ∘ (map-prod (gap f g c) (gap f' g' c')))
triangle-map-prod-cone {B' = B'}
  f g (pair p (pair q H)) f' g' (pair p' (pair q' H')) (pair z z') =
  eq-pair-Σ refl (eq-pair-Σ refl right-unit)

abstract
  is-equiv-map-prod-cone :
    {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
    is-equiv (map-prod-cone f g f' g')
  is-equiv-map-prod-cone f g f' g' =
    is-equiv-comp
      ( map-prod-cone f g f' g')
      ( tot ( λ t →
        ( tot (λ s → eq-pair')) ∘
        ( map-interchange-Σ-Σ _)))
      ( map-interchange-Σ-Σ _)
      ( refl-htpy)
      ( is-equiv-map-interchange-Σ-Σ _)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ t → is-equiv-comp
          ( ( tot (λ s → eq-pair')) ∘
            ( map-interchange-Σ-Σ
              ( λ y p y' → Id (f' (pr2 t)) (g' y'))))
          ( tot (λ s → eq-pair'))
          ( map-interchange-Σ-Σ
            ( λ y p y' → Id (f' (pr2 t)) (g' y')))
          ( refl-htpy)
          ( is-equiv-map-interchange-Σ-Σ _)
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ s → is-equiv-comp
              ( eq-pair')
              ( eq-pair')
              ( id)
              ( refl-htpy)
              ( is-equiv-id)
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
      ( map-prod f f') (map-prod g g') (prod-cone f g f' g' c c')
  is-pullback-prod-is-pullback-pair f g c f' g' c' is-pb-c is-pb-c' =
    is-equiv-comp
      ( gap (map-prod f f') (map-prod g g') (prod-cone f g f' g' c c'))
      ( map-prod-cone f g f' g')
      ( map-prod (gap f g c) (gap f' g' c'))
      ( triangle-map-prod-cone f g c f' g' c')
      ( is-equiv-map-prod _ _ is-pb-c is-pb-c')
      ( is-equiv-map-prod-cone f g f' g')
  
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
      ( prod-cone f g f' g' c c') →
    canonical-pullback f' g' → is-pullback f g c
  is-pullback-left-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t =
    is-equiv-left-factor-is-equiv-map-prod (gap f g c) (gap f' g' c') t
      ( is-equiv-right-factor
        ( gap
          ( map-prod f f')
          ( map-prod g g')
          ( prod-cone f g f' g' c c'))
      ( map-prod-cone f g f' g')
        ( map-prod (gap f g c) (gap f' g' c'))
        ( triangle-map-prod-cone f g c f' g' c')
        ( is-equiv-map-prod-cone f g f' g')
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
      ( prod-cone f g f' g' c c') →
    canonical-pullback f g → is-pullback f' g' c'
  is-pullback-right-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t =
    is-equiv-right-factor-is-equiv-map-prod (gap f g c) (gap f' g' c') t
      ( is-equiv-right-factor
        ( gap
          ( map-prod f f')
          ( map-prod g g')
          ( prod-cone f g f' g' c c'))
        ( map-prod-cone f g f' g')
        ( map-prod (gap f g c) (gap f' g' c'))
        ( triangle-map-prod-cone f g c f' g' c')
        ( is-equiv-map-prod-cone f g f' g')
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
