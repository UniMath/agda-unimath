---
title: Pullbacks
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.pullbacks where

open import foundation-core.pullbacks public

open import foundation.contractible-types using
  ( is-contr; is-contr-total-path; is-contr-equiv'; is-contr-is-equiv')
open import foundation.constant-maps using (const)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; triple)
open import foundation.diagonal-maps-of-types using (diagonal)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.function-extensionality using
  ( htpy-eq; issec-eq-htpy; isretr-eq-htpy)
open import foundation.functions using (_∘_; id; map-Π)
open import foundation.functoriality-dependent-function-types using
  ( map-inv-is-equiv-precomp-Π-is-equiv; htpy-map-Π;
    isretr-map-inv-is-equiv-precomp-Π-is-equiv;
    issec-map-inv-is-equiv-precomp-Π-is-equiv; is-equiv-map-Π)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using
  ( _~_; refl-htpy; right-unit-htpy; _∙h_; _·l_; _·r_; ap-concat-htpy;
    ap-concat-htpy'; inv-htpy; concat-htpy; concat-htpy';
    is-equiv-concat-htpy'; is-equiv-concat-htpy; refl-htpy'; ind-htpy;
    htpy-right-whisk; comp-htpy)
open import foundation.identity-types using
  ( Id; _＝_; refl; ap; _∙_; inv; right-unit; equiv-concat'; equiv-inv; concat';
    concat; is-equiv-concat; is-equiv-concat'; assoc; inv-con; con-inv; tr)
open import foundation.structure-identity-principle using (extensionality-Σ)
open import foundation.type-theoretic-principle-of-choice using
  ( map-distributive-Π-Σ; mapping-into-Σ; is-equiv-mapping-into-Σ;
    is-equiv-map-distributive-Π-Σ)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.cones-pullbacks
open import foundation-core.equivalences using
  ( is-equiv-comp; _∘e_; is-equiv; map-inv-is-equiv; _≃_; id-equiv;
    map-inv-equiv; is-equiv-has-inverse; is-equiv-right-factor;
    is-equiv-left-factor)
open import foundation-core.function-extensionality using
  ( eq-htpy; eq-htpy-refl-htpy)
open import foundation-core.functoriality-dependent-pair-types using
  ( tot; is-equiv-tot-is-fiberwise-equiv; equiv-tot)
open import foundation-core.universal-property-pullbacks using
  ( universal-property-pullback;
    is-equiv-up-pullback-up-pullback; up-pullback-up-pullback-is-equiv)
```

## Idea

We construct canonical pullbacks of cospans

## Properties

### Identity types can be presented as pullbacks

```agda
cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  cone (const unit A x) (const unit A y) (x ＝ y)
cone-Id x y =
  triple (const (x ＝ y) unit star) (const (x ＝ y) unit star) id

inv-gap-cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  canonical-pullback (const unit A x) (const unit A y) → x ＝ y
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
  cone (const unit (A × A) t) (diagonal A) (pr1 t ＝ pr2 t)
cone-Id' {A = A} (pair x y) =
  triple
    ( const (x ＝ y) unit star)
    ( const (x ＝ y) A x)
    ( λ p → eq-pair-Σ refl (inv p))

inv-gap-cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  canonical-pullback (const unit (A × A) t) (diagonal A) → (pr1 t ＝ pr2 t)
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
```

### The equivalence on canonical pullbacks induced by parallel cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} 
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  map-equiv-canonical-pullback-htpy :
    canonical-pullback f' g' → canonical-pullback f g
  map-equiv-canonical-pullback-htpy =
    tot (λ a → tot (λ b →
      ( concat' (f a) (inv (Hg b))) ∘ (concat (Hf a) (g' b))))

  abstract
    is-equiv-map-equiv-canonical-pullback-htpy :
      is-equiv map-equiv-canonical-pullback-htpy
    is-equiv-map-equiv-canonical-pullback-htpy =
      is-equiv-tot-is-fiberwise-equiv (λ a →
        is-equiv-tot-is-fiberwise-equiv (λ b →
          is-equiv-comp
            ( (concat' (f a) (inv (Hg b))) ∘ (concat (Hf a) (g' b)))
            ( concat' (f a) (inv (Hg b)))
            ( concat (Hf a) (g' b))
            ( refl-htpy)
            ( is-equiv-concat (Hf a) (g' b))
            ( is-equiv-concat' (f a) (inv (Hg b)))))

  equiv-canonical-pullback-htpy :
    canonical-pullback f' g' ≃ canonical-pullback f g
  pr1 equiv-canonical-pullback-htpy = map-equiv-canonical-pullback-htpy
  pr2 equiv-canonical-pullback-htpy = is-equiv-map-equiv-canonical-pullback-htpy
```

### Parallel pullback squares

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} 
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  triangle-is-pullback-htpy :
    {l4 : Level} {C : UU l4}
    {c : cone f g C} {c' : cone f' g' C} (Hc : htpy-parallel-cone Hf Hg c c') →
    (gap f g c) ~ (map-equiv-canonical-pullback-htpy Hf Hg ∘ (gap f' g' c'))
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
      {l4 : Level} {C : UU l4} {c : cone f g C} (c' : cone f' g' C)
      (Hc : htpy-parallel-cone Hf Hg c c') →
      is-pullback f' g' c' → is-pullback f g c
    is-pullback-htpy
      {c = pair p (pair q H)} (pair p' (pair q' H'))
      (pair Hp (pair Hq HH)) is-pb-c' =
      is-equiv-comp
        ( gap f g (triple p q H))
        ( map-equiv-canonical-pullback-htpy Hf Hg)
        ( gap f' g' (triple p' q' H'))
        ( triangle-is-pullback-htpy
          {c = triple p q H} {triple p' q' H'} (triple Hp Hq HH))
        ( is-pb-c')
        ( is-equiv-map-equiv-canonical-pullback-htpy Hf Hg)

  abstract
    is-pullback-htpy' :
      {l4 : Level} {C : UU l4} (c : cone f g C) {c' : cone f' g' C}
      (Hc : htpy-parallel-cone Hf Hg c c') →
      is-pullback f g c → is-pullback f' g' c'
    is-pullback-htpy'
      (pair p (pair q H)) {pair p' (pair q' H')}
      (pair Hp (pair Hq HH)) is-pb-c =
      is-equiv-right-factor
        ( gap f g (triple p q H))
        ( map-equiv-canonical-pullback-htpy Hf Hg)
        ( gap f' g' (triple p' q' H'))
        ( triangle-is-pullback-htpy
          {c = triple p q H} {triple p' q' H'} (triple Hp Hq HH))
        ( is-equiv-map-equiv-canonical-pullback-htpy Hf Hg)
        ( is-pb-c)

{- In the following part we will relate the type htpy-parallel-cone to the Identity
   type of cones. Here we will rely on function extensionality. -}

refl-htpy-parallel-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  htpy-parallel-cone (refl-htpy {f = f}) (refl-htpy {f = g}) c c
refl-htpy-parallel-cone f g c =
  triple refl-htpy refl-htpy right-unit-htpy

htpy-eq-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  c ＝ c' → htpy-parallel-cone (refl-htpy {f = f}) (refl-htpy {f = g}) c c'
htpy-eq-square f g c .c refl =
  triple refl-htpy refl-htpy right-unit-htpy

htpy-parallel-cone-refl-htpy-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) →
  (c c' : cone f g C) →
  htpy-cone f g c c' → htpy-parallel-cone (refl-htpy {f = f}) (refl-htpy {f = g}) c c'
htpy-parallel-cone-refl-htpy-htpy-cone f g
  (pair p (pair q H)) (pair p' (pair q' H')) =
  tot
    ( λ K → tot
      ( λ L M → ( ap-concat-htpy H _ _ right-unit-htpy) ∙h
        ( M ∙h ap-concat-htpy' _ _ H' (inv-htpy right-unit-htpy))))

abstract
  is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) →
    (c c' : cone f g C) →
    is-equiv (htpy-parallel-cone-refl-htpy-htpy-cone f g c c')
  is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone f g
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
  is-contr-total-htpy-parallel-cone-refl-htpy-refl-htpy :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) →
    (c : cone f g C) →
    is-contr (Σ (cone f g C) (htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c))
  is-contr-total-htpy-parallel-cone-refl-htpy-refl-htpy {A = A} {B} {X} {C}
    f g (pair p (pair q H)) =
    let c = triple p q H in
    is-contr-is-equiv'
      ( Σ (cone f g C) (htpy-cone f g c))
      ( tot (htpy-parallel-cone-refl-htpy-htpy-cone f g c))
      ( is-equiv-tot-is-fiberwise-equiv
        ( is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone f g c))
      ( is-contr-total-htpy-cone f g c)

abstract
  is-contr-total-htpy-parallel-cone-refl-htpy :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) →
    is-contr (Σ (cone f g' C) (htpy-parallel-cone (refl-htpy' f) Hg c))
  is-contr-total-htpy-parallel-cone-refl-htpy {C = C} f {g} =
    ind-htpy g
      ( λ g'' Hg' → ( c : cone f g C) →
        is-contr (Σ (cone f g'' C) (htpy-parallel-cone (refl-htpy' f) Hg' c)))
      ( is-contr-total-htpy-parallel-cone-refl-htpy-refl-htpy f g)

abstract
  is-contr-total-htpy-parallel-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) →
    is-contr (Σ (cone f' g' C) (htpy-parallel-cone Hf Hg c))
  is-contr-total-htpy-parallel-cone {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg =
    ind-htpy
      { A = A}
      { B = λ t → X}
      ( f)
      ( λ f'' Hf' → (g g' : B → X) (Hg : g ~ g') (c : cone f g C) →
        is-contr (Σ (cone f'' g' C) (htpy-parallel-cone Hf' Hg c)))
      ( λ g g' Hg → is-contr-total-htpy-parallel-cone-refl-htpy f Hg)
      Hf g g' Hg

tr-tr-refl-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy (refl-htpy {f = f})) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (refl-htpy {f = g})) tr-c
  in
  tr-tr-c ＝ c
tr-tr-refl-htpy-cone {C = C} f g c =
  let tr-c = tr (λ f''' → cone f''' g C) (eq-htpy refl-htpy) c
      tr-tr-c = tr (λ g'' → cone f g'' C) (eq-htpy refl-htpy) tr-c
      α : tr-tr-c ＝ tr-c
      α = ap (λ t → tr (λ g'' → cone f g'' C) t tr-c) (eq-htpy-refl-htpy g)
      β : tr-c ＝ c
      β = ap (λ t → tr (λ f''' → cone f''' g C) t c) (eq-htpy-refl-htpy f)
  in
  α ∙ β

htpy-eq-square-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy (refl-htpy {f = f})) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (refl-htpy {f = g})) tr-c
  in
  tr-tr-c ＝ c' → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c'
htpy-eq-square-refl-htpy f g c c' =
  map-inv-is-equiv-precomp-Π-is-equiv
    ( λ (p : Id c c') → (tr-tr-refl-htpy-cone f g c) ∙ p)
    ( is-equiv-concat (tr-tr-refl-htpy-cone f g c) c')
    ( λ p → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c')
    ( htpy-eq-square f g c c')

comp-htpy-eq-square-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  ( (htpy-eq-square-refl-htpy f g c c') ∘
    (concat (tr-tr-refl-htpy-cone f g c) c')) ~
  ( htpy-eq-square f g c c')
comp-htpy-eq-square-refl-htpy f g c c' =
  issec-map-inv-is-equiv-precomp-Π-is-equiv
    ( λ (p : Id c c') → (tr-tr-refl-htpy-cone f g c) ∙ p)
    ( is-equiv-concat (tr-tr-refl-htpy-cone f g c) c')
    ( λ p → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c')
    ( htpy-eq-square f g c c')
  
abstract
  htpy-parallel-cone-eq' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f g' C) →
    let tr-c    = tr (λ x → cone x g C) (eq-htpy (refl-htpy {f = f})) c
        tr-tr-c = tr (λ y → cone f y C) (eq-htpy Hg) tr-c
    in
    tr-tr-c ＝ c' → htpy-parallel-cone (refl-htpy' f) Hg c c'
  htpy-parallel-cone-eq' {C = C} f {g} =
    ind-htpy g
      ( λ g'' Hg' →
        ( c : cone f g C) (c' : cone f g'' C) →
        Id ( tr
             ( λ g'' → cone f g'' C)
             ( eq-htpy Hg')
             ( tr (λ f''' → cone f''' g C) (eq-htpy (refl-htpy' f)) c))
           ( c') →
        htpy-parallel-cone refl-htpy Hg' c c')
      ( htpy-eq-square-refl-htpy f g)

  comp-htpy-parallel-cone-eq' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c c' : cone f g C) →
    ( ( htpy-parallel-cone-eq' f refl-htpy c c') ∘
      ( concat (tr-tr-refl-htpy-cone f g c) c')) ~
    ( htpy-eq-square f g c c')
  comp-htpy-parallel-cone-eq' {A = A} {B} {X} {C} f g c c' =
    htpy-right-whisk
      ( htpy-eq (htpy-eq (htpy-eq (comp-htpy g
        ( λ g'' Hg' →
          ( c : cone f g C) (c' : cone f g'' C) →
            Id (tr (λ g'' → cone f g'' C) (eq-htpy Hg')
              ( tr (λ f''' → cone f''' g C) (eq-htpy (refl-htpy' f)) c)) c' →
          htpy-parallel-cone refl-htpy Hg' c c')
      ( htpy-eq-square-refl-htpy f g)) c) c'))
      ( concat (tr-tr-refl-htpy-cone f g c) c') ∙h
    ( comp-htpy-eq-square-refl-htpy f g c c')

abstract
  htpy-parallel-cone-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    let tr-c    = tr (λ x → cone x g C) (eq-htpy Hf) c
        tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
    in
    Id tr-tr-c c' → htpy-parallel-cone Hf Hg c c'
  htpy-parallel-cone-eq {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' p =
    ind-htpy f
    ( λ f'' Hf' →
      ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
      ( Id (tr (λ g'' → cone f'' g'' C) (eq-htpy Hg)
        ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c)) c') →
      htpy-parallel-cone Hf' Hg c c')
    ( λ g g' → htpy-parallel-cone-eq' f {g = g} {g' = g'})
    Hf g g' Hg c c' p
  
  comp-htpy-parallel-cone-eq : 
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c c' : cone f g C) →
    ( ( htpy-parallel-cone-eq refl-htpy refl-htpy c c') ∘
      ( concat (tr-tr-refl-htpy-cone f g c) c')) ~
    ( htpy-eq-square f g c c')
  comp-htpy-parallel-cone-eq {A = A} {B} {X} {C} f g c c' =
    htpy-right-whisk
      ( htpy-eq (htpy-eq (htpy-eq (htpy-eq (htpy-eq (htpy-eq (comp-htpy f
        ( λ f'' Hf' →
          ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
            ( Id ( tr (λ g'' → cone f'' g'' C) (eq-htpy Hg)
                 ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c)) c') →
            htpy-parallel-cone Hf' Hg c c')
        ( λ g g' → htpy-parallel-cone-eq' f {g = g} {g' = g'})) g) g)
        refl-htpy) c) c'))
      ( concat (tr-tr-refl-htpy-cone f g c) c') ∙h
      ( comp-htpy-parallel-cone-eq' f g c c')

abstract
  is-fiberwise-equiv-htpy-parallel-cone-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    is-equiv (htpy-parallel-cone-eq Hf Hg c c')
  is-fiberwise-equiv-htpy-parallel-cone-eq
    {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' =
    ind-htpy f
      ( λ f' Hf →
        ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f' g' C) →
          is-equiv (htpy-parallel-cone-eq Hf Hg c c'))
      ( λ g g' Hg c c' →
        ind-htpy g
          ( λ g' Hg →
            ( c : cone f g C) (c' : cone f g' C) →
              is-equiv (htpy-parallel-cone-eq refl-htpy Hg c c'))
          ( λ c c' →
            is-equiv-left-factor
              ( htpy-eq-square f g c c')
              ( htpy-parallel-cone-eq refl-htpy refl-htpy c c')
              ( concat (tr-tr-refl-htpy-cone f g c) c')
              ( inv-htpy (comp-htpy-parallel-cone-eq f g c c'))
              ( fundamental-theorem-id c
                ( refl-htpy-parallel-cone f g c)
                ( is-contr-total-htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c)
                ( htpy-eq-square f g c) c')
              ( is-equiv-concat (tr-tr-refl-htpy-cone f g c) c'))
          Hg c c')
      Hf g g' Hg c c'

eq-htpy-parallel-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f' g' C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy Hf) c
      tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
  in
  htpy-parallel-cone Hf Hg c c' → Id tr-tr-c c'
eq-htpy-parallel-cone Hf Hg c c' =
  map-inv-is-equiv
    { f = htpy-parallel-cone-eq Hf Hg c c'}
    ( is-fiberwise-equiv-htpy-parallel-cone-eq Hf Hg c c')
```

### Dependent products of pullbacks are pullbacks

```agda
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
```
