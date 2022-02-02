---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-foundations.13-function-extensionality-solutions where

open import univalent-foundations.13-function-extensionality public

-- Exercise 13.3

-- Exercise 13.3 (a)

associative-comp-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  (e : A ≃ B) (f : B ≃ C) (g : C ≃ D) →
  Id ((g ∘e f) ∘e e) (g ∘e (f ∘e e))
associative-comp-equiv e f g = eq-htpy-equiv refl-htpy

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  left-unit-law-equiv : (e : X ≃ Y) → Id (id-equiv ∘e e) e
  left-unit-law-equiv e = eq-htpy-equiv refl-htpy
  
  right-unit-law-equiv : (e : X ≃ Y) → Id (e ∘e id-equiv) e
  right-unit-law-equiv e = eq-htpy-equiv refl-htpy
  
  left-inverse-law-equiv : (e : X ≃ Y) → Id ((inv-equiv e) ∘e e) id-equiv
  left-inverse-law-equiv e =
    eq-htpy-equiv (isretr-map-inv-is-equiv (is-equiv-map-equiv e))
  
  right-inverse-law-equiv : (e : X ≃ Y) → Id (e ∘e (inv-equiv e)) id-equiv
  right-inverse-law-equiv e =
    eq-htpy-equiv (issec-map-inv-is-equiv (is-equiv-map-equiv e))

  inv-inv-equiv : (e : X ≃ Y) → Id (inv-equiv (inv-equiv e)) e
  inv-inv-equiv e = eq-htpy-equiv refl-htpy

  inv-inv-equiv' : (e : Y ≃ X) → Id (inv-equiv (inv-equiv e)) e
  inv-inv-equiv' e = eq-htpy-equiv refl-htpy

  is-equiv-inv-equiv : is-equiv (inv-equiv {A = X} {B = Y})
  is-equiv-inv-equiv =
    is-equiv-has-inverse
      ( inv-equiv)
      ( inv-inv-equiv')
      ( inv-inv-equiv)

  equiv-inv-equiv : (X ≃ Y) ≃ (Y ≃ X)
  pr1 equiv-inv-equiv = inv-equiv
  pr2 equiv-inv-equiv = is-equiv-inv-equiv

compose-inv-equiv-compose-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ B) →
  Id (inv-equiv f ∘e (f ∘e e)) e
compose-inv-equiv-compose-equiv f e =
  eq-htpy-equiv (λ x → isretr-map-inv-equiv f (map-equiv e x))

compose-equiv-compose-inv-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ C) →
  Id (f ∘e (inv-equiv f ∘e e)) e
compose-equiv-compose-inv-equiv f e =
  eq-htpy-equiv (λ x → issec-map-inv-equiv f (map-equiv e x))

is-equiv-comp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (A : UU l1) → is-equiv (λ (e : A ≃ B) → f ∘e e)
is-equiv-comp-equiv f A =
  is-equiv-has-inverse
    ( λ e → inv-equiv f ∘e e)
    ( compose-equiv-compose-inv-equiv f)
    ( compose-inv-equiv-compose-equiv f)

equiv-postcomp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3} →
  (f : B ≃ C) → (A : UU l1) → (A ≃ B) ≃ (A ≃ C)
pr1 (equiv-postcomp-equiv f A) e = f ∘e e
pr2 (equiv-postcomp-equiv f A) = is-equiv-comp-equiv f A

_⇔_ :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
P ⇔ Q = (pr1 P → pr1 Q) × (pr1 Q → pr1 P)

equiv-iff' :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (P ⇔ Q) → (pr1 P ≃ pr1 Q)
pr1 (equiv-iff' P Q t) = pr1 t
pr2 (equiv-iff' P Q t) = is-equiv-is-prop (pr2 P) (pr2 Q) (pr2 t)

equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (type-hom-Prop P Q) → (type-hom-Prop Q P) → pr1 P ≃ pr1 Q
equiv-iff P Q f g = equiv-iff' P Q (pair f g)

iff-equiv :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (pr1 P ≃ pr1 Q) → (P ⇔ Q)
pr1 (iff-equiv P Q e) = map-equiv e
pr2 (iff-equiv P Q e) = map-inv-equiv e

abstract
  is-prop-iff :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → is-prop (P ⇔ Q)
  is-prop-iff P Q =
    is-prop-prod
      ( is-prop-function-type (pr2 Q))
      ( is-prop-function-type (pr2 P))

abstract
  is-prop-equiv-Prop :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
    is-prop ((pr1 P) ≃ (pr1 Q))
  is-prop-equiv-Prop P Q =
    is-prop-equiv-is-prop (pr2 P) (pr2 Q)

abstract
  is-equiv-equiv-iff :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
    is-equiv (equiv-iff' P Q)
  is-equiv-equiv-iff P Q =
    is-equiv-is-prop
      ( is-prop-iff P Q)
      ( is-prop-equiv-Prop P Q)
      ( iff-equiv P Q)

equiv-equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (P ⇔ Q) ≃ (type-Prop P ≃ type-Prop Q)
pr1 (equiv-equiv-iff P Q) = equiv-iff' P Q
pr2 (equiv-equiv-iff P Q) = is-equiv-equiv-iff P Q

abstract
  is-prop-is-contr-endomaps :
    {l : Level} (P : UU l) → is-contr (P → P) → is-prop P
  is-prop-is-contr-endomaps P H =
    is-prop-all-elements-equal (λ x → htpy-eq (eq-is-contr H))

abstract
  is-contr-endomaps-is-prop :
    {l : Level} (P : UU l) → is-prop P → is-contr (P → P)
  is-contr-endomaps-is-prop P is-prop-P =
    is-proof-irrelevant-is-prop (is-prop-function-type is-prop-P) id

-- Bureaucracy

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  is-prop-is-injective :
    is-set A → (f : A → B) → is-prop (is-injective f)
  is-prop-is-injective H f =
    is-prop-Π'
      ( λ x →
        is-prop-Π'
          ( λ y → is-prop-function-type (H x y)))

  is-injective-Prop : is-set A → (A → B) → UU-Prop (l1 ⊔ l2)
  pr1 (is-injective-Prop H f) = is-injective f
  pr2 (is-injective-Prop H f) = is-prop-is-injective H f
  
  is-prop-is-emb : (f : A → B) → is-prop (is-emb f)
  is-prop-is-emb f =
    is-prop-Π (λ x → is-prop-Π (λ y → is-subtype-is-equiv (ap f)))

  is-emb-Prop : (A → B) → UU-Prop (l1 ⊔ l2)
  pr1 (is-emb-Prop f) = is-emb f
  pr2 (is-emb-Prop f) = is-prop-is-emb f

  is-prop-is-trunc-map : (k : 𝕋) (f : A → B) → is-prop (is-trunc-map k f)
  is-prop-is-trunc-map k f = is-prop-Π (λ x → is-prop-is-trunc k (fib f x))

  is-prop-is-contr-map : (f : A → B) → is-prop (is-contr-map f)
  is-prop-is-contr-map f = is-prop-is-trunc-map neg-two-𝕋 f

  is-prop-is-prop-map : (f : A → B) → is-prop (is-prop-map f)
  is-prop-is-prop-map f = is-prop-is-trunc-map neg-one-𝕋 f

  is-trunc-map-Prop : (k : 𝕋) → (A → B) → UU-Prop (l1 ⊔ l2)
  pr1 (is-trunc-map-Prop k f) = is-trunc-map k f
  pr2 (is-trunc-map-Prop k f) = is-prop-is-trunc-map k f

  is-contr-map-Prop : (A → B) → UU-Prop (l1 ⊔ l2)
  pr1 (is-contr-map-Prop f) = is-contr-map f
  pr2 (is-contr-map-Prop f) = is-prop-is-contr-map f

  is-prop-map-Prop : (A → B) → UU-Prop (l1 ⊔ l2)
  pr1 (is-prop-map-Prop f) = is-prop-map f
  pr2 (is-prop-map-Prop f) = is-prop-is-prop-map f

  equiv-is-equiv-is-contr-map : (f : A → B) → is-contr-map f ≃ is-equiv f
  equiv-is-equiv-is-contr-map f =
    equiv-iff
      ( is-contr-map-Prop f)
      ( is-equiv-Prop f)
      ( is-equiv-is-contr-map)
      ( is-contr-map-is-equiv)

  equiv-is-contr-map-is-equiv : (f : A → B) → is-equiv f ≃ is-contr-map f
  equiv-is-contr-map-is-equiv f =
    equiv-iff
      ( is-equiv-Prop f)
      ( is-contr-map-Prop f)
      ( is-contr-map-is-equiv)
      ( is-equiv-is-contr-map)

  equiv-is-emb-is-prop-map : (f : A → B) → is-prop-map f ≃ is-emb f
  equiv-is-emb-is-prop-map f =
    equiv-iff
      ( is-prop-map-Prop f)
      ( is-emb-Prop f)
      ( is-emb-is-prop-map)
      ( is-prop-map-is-emb)

  equiv-is-prop-map-is-emb : (f : A → B) → is-emb f ≃ is-prop-map f
  equiv-is-prop-map-is-emb f =
    equiv-iff
      ( is-emb-Prop f)
      ( is-prop-map-Prop f)
      ( is-prop-map-is-emb)
      ( is-emb-is-prop-map)

equiv-subtype-equiv :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (e : A ≃ B)
  (C : A → UU-Prop l3) (D : B → UU-Prop l4) →
  ((x : A) → type-Prop (C x) ↔ type-Prop (D (map-equiv e x))) →
  type-subtype C ≃ type-subtype D
equiv-subtype-equiv e C D H =
  equiv-Σ (λ y → type-Prop (D y)) e
    ( λ x → equiv-iff' (C x) (D (map-equiv e x)) (H x))

equiv-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (B ≃ C) ≃ (A ≃ C)
equiv-precomp-equiv e C =
  equiv-subtype-equiv
    ( equiv-precomp e C)
    ( is-equiv-Prop)
    ( is-equiv-Prop)
    ( λ g →
      pair
        ( is-equiv-comp' g (map-equiv e) (is-equiv-map-equiv e))
        ( λ is-equiv-eg →
          is-equiv-left-factor'
            g (map-equiv e) is-equiv-eg (is-equiv-map-equiv e)))

-- Exercise 13.5

abstract
  is-prop-is-path-split :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-path-split f)
  is-prop-is-path-split f =
    is-prop-is-proof-irrelevant (λ is-path-split-f →
      let is-equiv-f = is-equiv-is-path-split f is-path-split-f in
      is-contr-prod
        ( is-contr-sec-is-equiv is-equiv-f)
        ( is-contr-Π
          ( λ x → is-contr-Π
            ( λ y → is-contr-sec-is-equiv (is-emb-is-equiv is-equiv-f x y)))))

abstract
  is-equiv-is-path-split-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (is-path-split-is-equiv f)
  is-equiv-is-path-split-is-equiv f =
    is-equiv-is-prop
      ( is-subtype-is-equiv f)
      ( is-prop-is-path-split f)
      ( is-equiv-is-path-split f)

abstract
  is-prop-is-coherently-invertible :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-coherently-invertible f)
  is-prop-is-coherently-invertible {l1} {l2} {A} {B} f =
    is-prop-is-proof-irrelevant
      ( λ H →
        is-contr-equiv'
          ( Σ (sec f)
            ( λ sf → Σ (((pr1 sf) ∘ f) ~ id)
              ( λ H → (htpy-right-whisk (pr2 sf) f) ~ (htpy-left-whisk f H))))
          ( assoc-Σ (B → A)
            ( λ g → ((f ∘ g) ~ id))
            ( λ sf → Σ (((pr1 sf) ∘ f) ~ id)
              ( λ H → (htpy-right-whisk (pr2 sf) f) ~ (htpy-left-whisk f H))))
          ( is-contr-Σ
            ( is-contr-sec-is-equiv (E H))
            ( pair (g H) (G H))
            ( is-contr-equiv'
              ( (x : A) →
                Σ ( Id (g H (f x)) x)
                  ( λ p → Id (G H (f x)) (ap f p)))
              ( distributive-Π-Σ)
              ( is-contr-Π
                ( λ x →
                  is-contr-equiv'
                    ( fib (ap f) (G H (f x)))
                    ( equiv-tot
                      ( λ p → equiv-inv (ap f p) (G H (f x))))
                    ( is-contr-map-is-equiv
                      ( is-emb-is-equiv (E H) (g H (f x)) x)
                      ( (G H) (f x))))))))
    where
    E : is-coherently-invertible f → is-equiv f
    E H = is-equiv-is-coherently-invertible H
    g : is-coherently-invertible f → (B → A)
    g H = pr1 H
    G : (H : is-coherently-invertible f) → (f ∘ g H) ~ id
    G H = pr1 (pr2 H)

abstract
  is-equiv-is-coherently-invertible-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (is-coherently-invertible-is-equiv {f = f})
  is-equiv-is-coherently-invertible-is-equiv f =
    is-equiv-is-prop
      ( is-subtype-is-equiv f)
      ( is-prop-is-coherently-invertible f)
      ( is-equiv-is-coherently-invertible)

-- Exercise 13.15 (b)

is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  (id {A = A} ~ id {A = A}) → has-inverse (id {A = A})
pr1 (is-invertible-id-htpy-id-id A H) = id
pr1 (pr2 (is-invertible-id-htpy-id-id A H)) = refl-htpy
pr2 (pr2 (is-invertible-id-htpy-id-id A H)) = H

triangle-is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  ( is-invertible-id-htpy-id-id A) ~
    ( ( map-assoc-Σ (A → A) (λ g → (id ∘ g) ~ id) (λ s → ((pr1 s) ∘ id) ~ id)) ∘
      ( map-inv-left-unit-law-Σ-is-contr
        { B = λ s → ((pr1 s) ∘ id) ~ id}
        ( is-contr-sec-is-equiv (is-equiv-id {_} {A}))
        ( pair id refl-htpy)))
triangle-is-invertible-id-htpy-id-id A H = refl

abstract
  is-equiv-invertible-id-htpy-id-id :
    {l : Level} (A : UU l) → is-equiv (is-invertible-id-htpy-id-id A)
  is-equiv-invertible-id-htpy-id-id A =
    is-equiv-comp
      ( is-invertible-id-htpy-id-id A)
      ( map-assoc-Σ (A → A) (λ g → (id ∘ g) ~ id) (λ s → ((pr1 s) ∘ id) ~ id))
      ( map-inv-left-unit-law-Σ-is-contr
        ( is-contr-sec-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( triangle-is-invertible-id-htpy-id-id A)
      ( is-equiv-map-inv-left-unit-law-Σ-is-contr
        ( is-contr-sec-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( is-equiv-map-assoc-Σ _ _ _)

-- Exercise 13.6

module _
  {l1 : Level} (A : UU l1)
  where

  dependent-universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-empty l =
    (P : A → UU l) → is-contr ((x : A) → P x)

  universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  universal-property-empty l = (X : UU l) → is-contr (A → X)

  universal-property-dependent-universal-property-empty :
    ({l : Level} → dependent-universal-property-empty l) →
    ({l : Level} → universal-property-empty l)
  universal-property-dependent-universal-property-empty dup-empty {l} X =
    dup-empty {l} (λ a → X)

  is-empty-universal-property-empty :
    ({l : Level} → universal-property-empty l) → is-empty A
  is-empty-universal-property-empty up-empty = center (up-empty empty)

  dependent-universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → dependent-universal-property-empty l
  pr1 (dependent-universal-property-empty-is-empty {l} H P) x = ex-falso (H x)
  pr2 (dependent-universal-property-empty-is-empty {l} H P) f =
    eq-htpy (λ x → ex-falso (H x))
  
  universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → universal-property-empty l
  universal-property-empty-is-empty {l} H =
    universal-property-dependent-universal-property-empty
      ( dependent-universal-property-empty-is-empty H)

abstract
  dependent-universal-property-empty' :
    {l : Level} (P : empty → UU l) → is-contr ((x : empty) → P x)
  pr1 (dependent-universal-property-empty' P) = ind-empty {P = P}
  pr2 (dependent-universal-property-empty' P) f = eq-htpy ind-empty

abstract
  universal-property-empty' :
    {l : Level} (X : UU l) → is-contr (empty → X)
  universal-property-empty' X =
    dependent-universal-property-empty' (λ t → X)

abstract
  uniqueness-empty :
    {l : Level} (Y : UU l) → ((l' : Level) (X : UU l') →
    is-contr (Y → X)) → is-equiv (ind-empty {P = λ t → Y})
  uniqueness-empty Y H =
    is-equiv-is-equiv-precomp ind-empty
      ( λ l X → is-equiv-is-contr
        ( λ g → g ∘ ind-empty)
        ( H _ X)
        ( universal-property-empty' X))

abstract
  universal-property-empty-is-equiv-ind-empty :
    {l : Level} (X : UU l) → is-equiv (ind-empty {P = λ t → X}) →
    ((l' : Level) (Y : UU l') → is-contr (X → Y))
  universal-property-empty-is-equiv-ind-empty X is-equiv-ind-empty l' Y =
    is-contr-is-equiv
      ( empty → Y)
      ( λ f → f ∘ ind-empty)
      ( is-equiv-precomp-is-equiv ind-empty is-equiv-ind-empty Y)
      ( universal-property-empty' Y)

-- Exercise 13.5

module _
  {l1 : Level} {A : UU l1}
  where

  ev-point : {l2 : Level} (a : A) {P : A → UU l2} → ((x : A) → P x) → P a
  ev-point a f = f a

  ev-point' : {l2 : Level} (a : A) {X : UU l2} → (A → X) → X
  ev-point' a f = f a

  dependent-universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-contr l a =
    (P : A → UU l) → is-equiv (ev-point a {P})

  universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  universal-property-contr l a =
    (X : UU l) → is-equiv (ev-point' a {X})

  universal-property-dependent-universal-property-contr :
    (a : A) →
    ({l : Level} → dependent-universal-property-contr l a) →
    ({l : Level} → universal-property-contr l a)
  universal-property-dependent-universal-property-contr a dup-contr {l} X =
    dup-contr {l} (λ x → X)

  abstract
    is-equiv-ev-point-universal-property-contr :
      (a : A) → ({l : Level} → universal-property-contr l a) →
      is-equiv (ev-point' a {A})
    is-equiv-ev-point-universal-property-contr a up-contr =
      up-contr A

  abstract
    is-contr-is-equiv-ev-point :
      (a : A) → is-equiv (ev-point' a {X = A}) → is-contr A
    pr1 (is-contr-is-equiv-ev-point a H) = a
    pr2 (is-contr-is-equiv-ev-point a H) =
      htpy-eq
        ( ap
          ( pr1)
          ( eq-is-contr'
            ( is-contr-map-is-equiv H a)
            ( pair (λ x → a) refl)
            ( pair id refl)))

  abstract
    is-contr-universal-property-contr :
      (a : A) →
      ({l : Level} → universal-property-contr l a) → is-contr A
    is-contr-universal-property-contr a up-contr =
      is-contr-is-equiv-ev-point a
        ( is-equiv-ev-point-universal-property-contr a up-contr)

  abstract
    is-contr-dependent-universal-property-contr :
      (a : A) →
      ({l : Level} → dependent-universal-property-contr l a) → is-contr A
    is-contr-dependent-universal-property-contr a dup-contr =
      is-contr-universal-property-contr a
        ( universal-property-dependent-universal-property-contr a dup-contr)

  abstract
    dependent-universal-property-contr-is-contr :
      (a : A) → is-contr A →
      {l : Level} → dependent-universal-property-contr l a
    dependent-universal-property-contr-is-contr a H {l} P =
      is-equiv-has-inverse
        ( ind-singleton-is-contr a H P)
        ( comp-singleton-is-contr a H P)
        ( λ f →
          eq-htpy
            ( ind-singleton-is-contr a H
              ( λ x → Id (ind-singleton-is-contr a H P (f a) x) (f x))
              ( comp-singleton-is-contr a H P (f a))))

  abstract
    universal-property-contr-is-contr :
      (a : A) → is-contr A → {l : Level} → universal-property-contr l a
    universal-property-contr-is-contr a H =
      universal-property-dependent-universal-property-contr a
        ( dependent-universal-property-contr-is-contr a H)

  equiv-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (X : UU l) → (A → X) ≃ X
  pr1 (equiv-universal-property-contr a H X) = ev-point' a
  pr2 (equiv-universal-property-contr a H X) =
    universal-property-contr-is-contr a H X

  abstract
    is-equiv-self-diagonal-is-equiv-diagonal :
      ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) →
      is-equiv (λ x → const A A x)
    is-equiv-self-diagonal-is-equiv-diagonal H = H A

  abstract
    is-contr-is-equiv-self-diagonal :
      is-equiv (λ x → const A A x) → is-contr A
    is-contr-is-equiv-self-diagonal H =
      tot (λ x → htpy-eq) (center (is-contr-map-is-equiv H id))

  abstract
    is-contr-is-equiv-diagonal :
      ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) → is-contr A
    is-contr-is-equiv-diagonal H =
      is-contr-is-equiv-self-diagonal
        ( is-equiv-self-diagonal-is-equiv-diagonal H)

  abstract
    is-equiv-diagonal-is-contr :
      is-contr A →
      {l : Level} (X : UU l) → is-equiv (λ x → const A X x)
    is-equiv-diagonal-is-contr H X =
      is-equiv-has-inverse
        ( ev-point' (center H))
        ( λ f → eq-htpy (λ x → ap f (contraction H x)))
        ( λ x → refl)

  equiv-diagonal-is-contr :
    {l : Level} (X : UU l) → is-contr A → X ≃ (A → X)
  pr1 (equiv-diagonal-is-contr X H) = const A X
  pr2 (equiv-diagonal-is-contr X H) = is-equiv-diagonal-is-contr H X

-- We conclude that the properties in the exercise hold for the unit type

ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) → P star
ev-star P f = f star

ev-star' :
  {l : Level} (Y : UU l) → (unit → Y) → Y
ev-star' Y = ev-star (λ t → Y)

pt : {l1 : Level} {X : UU l1} (x : X) → unit → X
pt x y = x

abstract
  dependent-universal-property-unit :
    {l : Level} (P : unit → UU l) → is-equiv (ev-star P)
  dependent-universal-property-unit =
    dependent-universal-property-contr-is-contr star is-contr-unit

equiv-dependent-universal-property-unit :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) ≃ P star
pr1 (equiv-dependent-universal-property-unit P) = ev-star P
pr2 (equiv-dependent-universal-property-unit P) =
  dependent-universal-property-unit P

abstract
  universal-property-unit :
    {l : Level} (Y : UU l) → is-equiv (ev-star' Y)
  universal-property-unit Y = dependent-universal-property-unit (λ t → Y)

equiv-universal-property-unit :
  {l : Level} (Y : UU l) → (unit → Y) ≃ Y
pr1 (equiv-universal-property-unit Y) = ev-star' Y
pr2 (equiv-universal-property-unit Y) = universal-property-unit Y

abstract
  is-equiv-pt-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X → is-equiv (pt x)
  is-equiv-pt-is-contr x is-contr-X =
    is-equiv-is-contr (pt x) is-contr-unit is-contr-X

abstract
  is-equiv-pt-universal-property-unit :
    {l1 : Level} (X : UU l1) (x : X) →
    ((l2 : Level) (Y : UU l2) → is-equiv (λ (f : X → Y) → f x)) →
    is-equiv (pt x)
  is-equiv-pt-universal-property-unit X x H =
    is-equiv-is-equiv-precomp
      ( pt x)
      ( λ l Y → is-equiv-right-factor'
        ( ev-star' Y)
        ( precomp (pt x) Y)
        ( universal-property-unit Y)
        ( H _ Y))

abstract
  universal-property-unit-is-equiv-pt :
    {l1 : Level} {X : UU l1} (x : X) →
    is-equiv (pt x) →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-equiv-pt x is-equiv-pt Y =
    is-equiv-comp
      ( λ f → f x)
      ( ev-star' Y)
      ( precomp (pt x) Y)
      ( λ f → refl)
      ( is-equiv-precomp-is-equiv (pt x) is-equiv-pt Y)
      ( universal-property-unit Y)

abstract
  universal-property-unit-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-contr x is-contr-X =
    universal-property-unit-is-equiv-pt x
      ( is-equiv-pt-is-contr x is-contr-X)

abstract
  is-equiv-diagonal-is-equiv-pt :
    {l1 : Level} {X : UU l1} (x : X) →
    is-equiv (pt x) →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ y → const X Y y))
  is-equiv-diagonal-is-equiv-pt {X = X} x is-equiv-pt Y =
    is-equiv-is-section
      ( universal-property-unit-is-equiv-pt x is-equiv-pt Y)
      ( refl-htpy)
  
-- Exercise 13.6

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  ev-inl-inr :
    {l3 : Level} (P : coprod A B → UU l3) →
    ((t : coprod A B) → P t) → ((x : A) → P (inl x)) × ((y : B) → P (inr y))
  ev-inl-inr P s = pair (λ x → s (inl x)) (λ y → s (inr y))

  abstract
    dependent-universal-property-coprod :
      {l3 : Level} (P : coprod A B → UU l3) → is-equiv (ev-inl-inr P)
    dependent-universal-property-coprod P =
      is-equiv-has-inverse
        ( λ p → ind-coprod P (pr1 p) (pr2 p))
        ( ind-Σ (λ f g → eq-pair refl refl))
        ( λ s → eq-htpy (ind-coprod _ (λ x → refl) λ y → refl))

  equiv-dependent-universal-property-coprod :
    {l3 : Level} (P : coprod A B → UU l3) →
    ((x : coprod A B) → P x) ≃ (((a : A) → P (inl a)) × ((b : B) → P (inr b)))
  pr1 (equiv-dependent-universal-property-coprod P) = ev-inl-inr P
  pr2 (equiv-dependent-universal-property-coprod P) =
    dependent-universal-property-coprod P

  abstract
    universal-property-coprod :
      {l3 : Level} (X : UU l3) →
      is-equiv (ev-inl-inr (λ (t : coprod A B) → X))
    universal-property-coprod X = dependent-universal-property-coprod (λ t → X)
  
  equiv-universal-property-coprod :
    {l3 : Level} (X : UU l3) →
    (coprod A B → X) ≃ ((A → X) × (B → X))
  equiv-universal-property-coprod X =
    equiv-dependent-universal-property-coprod (λ t → X)
  
  abstract
    uniqueness-coprod :
      {l3 : Level} {Y : UU l3} (i : A → Y) (j : B → Y) →
      ((l : Level) (X : UU l) →
        is-equiv (λ (s : Y → X) → pair' (s ∘ i) (s ∘ j))) →
      is-equiv (ind-coprod (λ t → Y) i j)
    uniqueness-coprod {Y = Y} i j H =
      is-equiv-is-equiv-precomp
        ( ind-coprod _ i j)
        ( λ l X → is-equiv-right-factor'
          ( ev-inl-inr (λ t → X))
          ( precomp (ind-coprod (λ t → Y) i j) X)
          ( universal-property-coprod X)
          ( H _ X))

  abstract
    universal-property-coprod-is-equiv-ind-coprod :
      {l3 : Level} (X : UU l3) (i : A → X) (j : B → X) →
      is-equiv (ind-coprod (λ t → X) i j) →
      (l4 : Level) (Y : UU l4) →
        is-equiv (λ (s : X → Y) → pair' (s ∘ i) (s ∘ j))
    universal-property-coprod-is-equiv-ind-coprod X i j H l Y =
      is-equiv-comp
        ( λ s → pair (s ∘ i) (s ∘ j))
        ( ev-inl-inr (λ t → Y))
        ( precomp (ind-coprod (λ t → X) i j) Y)
        ( λ s → refl)
        ( is-equiv-precomp-is-equiv
          ( ind-coprod (λ t → X) i j)
          ( H)
          ( Y))
        ( universal-property-coprod Y)

-- Exercise 13.7

module _
  {l : Level} {X : UU l} (x : X) (f : X → X)
  where

  structure-preserving-map-ℕ : UU l
  structure-preserving-map-ℕ =
    Σ (ℕ → X) (λ h → (Id (h zero-ℕ) x) × ((h ∘ succ-ℕ) ~ (f ∘ h)))

  htpy-structure-preserving-map-ℕ :
    (h k : structure-preserving-map-ℕ) → UU l
  htpy-structure-preserving-map-ℕ h k =
    Σ ( pr1 h ~ pr1 k)
      ( λ H →
        ( Id (pr1 (pr2 h)) (H zero-ℕ ∙ pr1 (pr2 k))) ×
        ( (n : ℕ) →
          Id (pr2 (pr2 h) n ∙ ap f (H n)) (H (succ-ℕ n) ∙ pr2 (pr2 k) n)))

  refl-htpy-structure-preserving-map-ℕ :
    (h : structure-preserving-map-ℕ) → htpy-structure-preserving-map-ℕ h h
  refl-htpy-structure-preserving-map-ℕ h =
    triple refl-htpy refl (λ n → right-unit)

  htpy-eq-structure-preserving-map-ℕ :
    {h k : structure-preserving-map-ℕ} → Id h k →
    htpy-structure-preserving-map-ℕ h k
  htpy-eq-structure-preserving-map-ℕ {h} refl =
    refl-htpy-structure-preserving-map-ℕ h

  is-contr-total-htpy-structure-preserving-map-ℕ :
    (h : structure-preserving-map-ℕ) →
    is-contr (Σ structure-preserving-map-ℕ (htpy-structure-preserving-map-ℕ h))
  is-contr-total-htpy-structure-preserving-map-ℕ h =
    is-contr-total-Eq-structure
      ( λ g p (H : pr1 h ~ g) →
        ( Id (pr1 (pr2 h)) (H zero-ℕ ∙ pr1 p)) ×
        ( (n : ℕ) →
          Id (pr2 (pr2 h) n ∙ ap f (H n)) (H (succ-ℕ n) ∙ pr2 p n)))
      ( is-contr-total-htpy (pr1 h))
      ( pair (pr1 h) refl-htpy)
      ( is-contr-total-Eq-structure
        ( λ p0 pS q →
          (n : ℕ) → Id (pr2 (pr2 h) n ∙ refl) (pS n))
        ( is-contr-total-path (pr1 (pr2 h)))
        ( pair (pr1 (pr2 h)) refl)
        ( is-contr-total-htpy (λ n → (pr2 (pr2 h) n ∙ refl))))

  is-equiv-htpy-eq-structure-preserving-map-ℕ :
    (h k : structure-preserving-map-ℕ) →
    is-equiv (htpy-eq-structure-preserving-map-ℕ {h} {k})
  is-equiv-htpy-eq-structure-preserving-map-ℕ h =
    fundamental-theorem-id h
      ( refl-htpy-structure-preserving-map-ℕ h)
      ( is-contr-total-htpy-structure-preserving-map-ℕ h)
      ( λ k → htpy-eq-structure-preserving-map-ℕ {h} {k})

  eq-htpy-structure-preserving-map-ℕ :
    {h k : structure-preserving-map-ℕ} →
    htpy-structure-preserving-map-ℕ h k → Id h k
  eq-htpy-structure-preserving-map-ℕ {h} {k} =
    map-inv-is-equiv (is-equiv-htpy-eq-structure-preserving-map-ℕ h k)

  center-structure-preserving-map-ℕ : structure-preserving-map-ℕ
  center-structure-preserving-map-ℕ = triple h p H
    where
    h : ℕ → X
    h zero-ℕ = x
    h (succ-ℕ n) = f (h n)
    p : Id (h zero-ℕ) x
    p = refl
    H : (h ∘ succ-ℕ) ~ (f ∘ h)
    H = refl-htpy

  contraction-structure-preserving-map-ℕ :
    (h : structure-preserving-map-ℕ) →
    Id center-structure-preserving-map-ℕ h
  contraction-structure-preserving-map-ℕ h =
    eq-htpy-structure-preserving-map-ℕ (triple α β γ)
    where
    α : pr1 center-structure-preserving-map-ℕ ~ pr1 h
    α zero-ℕ = inv (pr1 (pr2 h))
    α (succ-ℕ n) = ap f (α n) ∙ inv (pr2 (pr2 h) n)
    β : Id (pr1 (pr2 center-structure-preserving-map-ℕ)) (α zero-ℕ ∙ pr1 (pr2 h))
    β = inv (left-inv (pr1 (pr2 h)))
    γ : (n : ℕ) →
        Id ( pr2 (pr2 center-structure-preserving-map-ℕ) n ∙ ap f (α n))
           ( α (succ-ℕ n) ∙ pr2 (pr2 h) n)
    γ n = ( ( inv right-unit) ∙
            ( ap (λ q → (ap f (α n) ∙ q)) (inv (left-inv (pr2 (pr2 h) n))))) ∙
          ( inv (assoc (ap f (α n)) (inv (pr2 (pr2 h) n)) (pr2 (pr2 h) n)))

  is-contr-structure-preserving-map-ℕ : is-contr structure-preserving-map-ℕ
  pr1 is-contr-structure-preserving-map-ℕ = center-structure-preserving-map-ℕ
  pr2 is-contr-structure-preserving-map-ℕ =
    contraction-structure-preserving-map-ℕ
  
-- Exercise 13.8

-- We show that induction on ℕ implies ordinal induction.

□-<-ℕ :
  {l : Level} → (ℕ → UU l) → ℕ → UU l
□-<-ℕ P n = (m : ℕ) → (le-ℕ m n) → P m

reflect-□-<-ℕ :
  {l : Level} (P : ℕ → UU l) →
  (( n : ℕ) → □-<-ℕ P n) → (n : ℕ) → P n
reflect-□-<-ℕ P f n = f (succ-ℕ n) n (succ-le-ℕ n)

le-zero-ℕ :
  (m : ℕ) → (le-ℕ m zero-ℕ) → empty
le-zero-ℕ zero-ℕ ()
le-zero-ℕ (succ-ℕ m) ()

le-one-ℕ :
  (n : ℕ) → le-ℕ (succ-ℕ n) 1 → empty
le-one-ℕ zero-ℕ ()
le-one-ℕ (succ-ℕ n) ()

zero-ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) → □-<-ℕ P zero-ℕ
zero-ordinal-ind-ℕ P m t = ind-empty (le-zero-ℕ m t)

transitive-le-ℕ' :
  (k l m : ℕ) → (le-ℕ k l) → (le-ℕ l (succ-ℕ m)) → le-ℕ k m
transitive-le-ℕ' zero-ℕ zero-ℕ m () s
transitive-le-ℕ' (succ-ℕ k) zero-ℕ m () s
transitive-le-ℕ' zero-ℕ (succ-ℕ l) zero-ℕ star s = ind-empty (le-one-ℕ l s)
transitive-le-ℕ' (succ-ℕ k) (succ-ℕ l) zero-ℕ t s = ind-empty (le-one-ℕ l s)
transitive-le-ℕ' zero-ℕ (succ-ℕ l) (succ-ℕ m) star s = star
transitive-le-ℕ' (succ-ℕ k) (succ-ℕ l) (succ-ℕ m) t s =
  transitive-le-ℕ' k l m t s

succ-ordinal-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → ((n : ℕ) → (□-<-ℕ P n) → P n) →
  (k : ℕ) → □-<-ℕ P k → □-<-ℕ P (succ-ℕ k)
succ-ordinal-ind-ℕ P f k g m t =
  f m (λ m' t' → g m' (transitive-le-ℕ' m' m k t' t))

induction-ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( qS : (k : ℕ) → □-<-ℕ P k → □-<-ℕ P (succ-ℕ k))
  ( n : ℕ) → □-<-ℕ P n
induction-ordinal-ind-ℕ P qS zero-ℕ = zero-ordinal-ind-ℕ P 
induction-ordinal-ind-ℕ P qS (succ-ℕ n) =
  qS n (induction-ordinal-ind-ℕ P qS n)

ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( (n : ℕ) → (□-<-ℕ P n) → P n) →
  ( n : ℕ) → P n
ordinal-ind-ℕ P f =
  reflect-□-<-ℕ P
    ( induction-ordinal-ind-ℕ P (succ-ordinal-ind-ℕ P f))

-- Exercise 13.9

-- Definition of the postcomposition functions

postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X → Y) → (A → X) → (A → Y)
postcomp A f h = f ∘ h

map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → A i) → ((i : I) → B i)
map-Π f h i = f i (h i)

htpy-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {f f' : (i : I) → A i → B i} (H : (i : I) → (f i) ~ (f' i)) →
  (map-Π f) ~ (map-Π f')
htpy-map-Π H h = eq-htpy (λ i → H i (h i))

map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) → 
  ((i : I) → A i → B i) → ((j : J) → A (α j)) → ((j : J) → B (α j))
map-Π' α f = map-Π (λ j → f (α j))

htpy-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) {f f' : (i : I) → A i → B i} →
  ((i : I) → (f i) ~ (f' i)) → (map-Π' α f ~ map-Π' α f')
htpy-map-Π' α H = htpy-map-Π (λ j → H (α j))

-- Exercise 13.9 (a)

-- We compute the fiber of map-Π and then solve the exercise

equiv-fib-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) (h : (i : I) → B i) →
  ((i : I) → fib (f i) (h i)) ≃ fib (map-Π f) h
equiv-fib-map-Π f h =
  equiv-tot (λ x → equiv-eq-htpy) ∘e distributive-Π-Σ

is-trunc-map-map-Π :
  (k : 𝕋) {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π f)
is-trunc-map-map-Π k {I = I} f H h =
  is-trunc-equiv' k
    ( (i : I) → fib (f i) (h i))
    ( equiv-fib-map-Π f h)
    ( is-trunc-Π k (λ i → H i (h i)))

abstract
  is-equiv-map-Π :
    {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
    (f : (i : I) → A i → B i) (is-equiv-f : is-fiberwise-equiv f) →
    is-equiv (map-Π f)
  is-equiv-map-Π f is-equiv-f =
    is-equiv-is-contr-map
      ( is-trunc-map-map-Π neg-two-𝕋 f
        ( λ i → is-contr-map-is-equiv (is-equiv-f i)))

equiv-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → (A i) ≃ (B i)) → ((i : I) → A i) ≃ ((i : I) → B i)
pr1 (equiv-map-Π e) = map-Π (λ i → map-equiv (e i))
pr2 (equiv-map-Π e) = is-equiv-map-Π _ (λ i → is-equiv-map-equiv (e i))

module _
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a'))
  where
  
  map-equiv-Π : ((a' : A') → B' a') → ((a : A) → B a)
  map-equiv-Π =
    ( map-Π
      ( λ a →
        ( tr B (issec-map-inv-equiv e a)) ∘
        ( map-equiv (f (map-inv-equiv e a))))) ∘
    ( precomp-Π (map-inv-equiv e) B')

  compute-map-equiv-Π :
    (h : (a' : A') → B' a') (a' : A') →
    Id ( map-equiv-Π h (map-equiv e a')) (map-equiv (f a') (h a'))
  compute-map-equiv-Π h a' =
    ( ap
      ( λ t →
        tr B t ( map-equiv
                 ( f (map-inv-equiv e (map-equiv e a')))
                 ( h (map-inv-equiv e (map-equiv e a')))))
      ( coherence-map-inv-equiv e a')) ∙
    ( ( tr-ap
        ( map-equiv e)
        ( λ _ → id)
        ( isretr-map-inv-equiv e a')
        ( map-equiv
          ( f (map-inv-equiv e (map-equiv e a')))
          ( h (map-inv-equiv e (map-equiv e a'))))) ∙
      ( α ( map-inv-equiv e (map-equiv e a'))
          ( isretr-map-inv-equiv e a')))
    where
    α : (x : A') (p : Id x a') →
        Id ( tr (B ∘ map-equiv e) p (map-equiv (f x) (h x)))
           ( map-equiv (f a') (h a'))
    α x refl = refl

  abstract
    is-equiv-map-equiv-Π : is-equiv map-equiv-Π
    is-equiv-map-equiv-Π =
      is-equiv-comp'
        ( map-Π (λ a →
          ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a)) ∘
          ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))))
        ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')
        ( is-equiv-precomp-Π-is-equiv
          ( map-inv-is-equiv (is-equiv-map-equiv e))
          ( is-equiv-map-inv-is-equiv (is-equiv-map-equiv e))
          ( B'))
        ( is-equiv-map-Π _
          ( λ a → is-equiv-comp'
            ( tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a))
            ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
            ( is-equiv-map-equiv
              ( f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
            ( is-equiv-tr B (issec-map-inv-is-equiv (is-equiv-map-equiv e) a))))

  equiv-Π : ((a' : A') → B' a') ≃ ((a : A) → B a)
  pr1 equiv-Π = map-equiv-Π
  pr2 equiv-Π = is-equiv-map-equiv-Π

id-map-equiv-Π :
  { l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  ( map-equiv-Π B (id-equiv {A = A}) (λ a → id-equiv {A = B a})) ~ id
id-map-equiv-Π B h = eq-htpy (compute-map-equiv-Π B id-equiv (λ a → id-equiv) h)

-- Exercise 13.9 (b)

equiv-fib-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i)
  (h : (j : J) → B (α j)) →
  ((j : J) → fib (f (α j)) (h j)) ≃ fib (map-Π' α f) h
equiv-fib-map-Π' α f h =
  equiv-tot (λ x → equiv-eq-htpy) ∘e distributive-Π-Σ

is-trunc-map-map-Π-is-trunc-map' :
  (k : 𝕋) {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
  ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π' α f)
is-trunc-map-map-Π-is-trunc-map' k {J = J} α f H h =
  is-trunc-equiv' k
    ( (j : J) → fib (f (α j)) (h j))
    ( equiv-fib-map-Π' α f h)
    ( is-trunc-Π k (λ j → H (α j) (h j)))

is-trunc-map-is-trunc-map-map-Π' :
  (k : 𝕋) {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ({l : Level} {J : UU l} (α : J → I) → is-trunc-map k (map-Π' α f)) →
  (i : I) → is-trunc-map k (f i)
is-trunc-map-is-trunc-map-map-Π' k {A = A} {B} f H i b =
  is-trunc-equiv' k
    ( fib (map-Π (λ (x : unit) → f i)) (const unit (B i) b))
    ( equiv-Σ
      ( λ a → Id (f i a) b)
      ( equiv-universal-property-unit (A i))
      ( λ h → equiv-ap
        ( equiv-universal-property-unit (B i))
        ( map-Π (λ x → f i) h)
        ( const unit (B i) b)))
    ( H (λ x → i) (const unit (B i) b))

-- Exercise 13.9 (c)

is-trunc-map-postcomp-is-trunc-map :
  {l1 l2 l3 : Level} (k : 𝕋) (A : UU l3) {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-trunc-map k f → is-trunc-map k (postcomp A f)
is-trunc-map-postcomp-is-trunc-map k A {X} {Y} f is-trunc-f =
  is-trunc-map-map-Π-is-trunc-map' k
    ( const A unit star)
    ( const unit (X → Y) f)
    ( const unit (is-trunc-map k f) is-trunc-f)

is-trunc-map-is-trunc-map-postcomp :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {Y : UU l2} (f : X → Y) →
  ( {l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)) →
  is-trunc-map k f
is-trunc-map-is-trunc-map-postcomp k {X} {Y} f is-trunc-post-f =
  is-trunc-map-is-trunc-map-map-Π' k
    ( const unit (X → Y) f)
    ( λ {l} {J} α → is-trunc-post-f {l} J)
    ( star)

abstract
  is-equiv-is-equiv-postcomp :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f)) → is-equiv f
  is-equiv-is-equiv-postcomp {X = X} {Y = Y} f post-comp-equiv-f =
    is-equiv-is-contr-map
      ( is-trunc-map-is-trunc-map-postcomp neg-two-𝕋 f
        ( λ {l} A → is-contr-map-is-equiv (post-comp-equiv-f A)))

{- The following version of the same theorem works when X and Y are in the same
   universe. The condition of inducing equivalences by postcomposition is 
   simplified to that universe. -}

is-equiv-is-equiv-postcomp' :
  {l : Level} {X : UU l} {Y : UU l} (f : X → Y) →
  ((A : UU l) → is-equiv (postcomp A f)) → is-equiv f
is-equiv-is-equiv-postcomp'
  {l} {X} {Y} f is-equiv-postcomp-f =
  let sec-f = center (is-contr-map-is-equiv (is-equiv-postcomp-f Y) id)
  in
  is-equiv-has-inverse
    ( pr1 sec-f)
    ( htpy-eq (pr2 sec-f))
    ( htpy-eq
      ( ap ( pr1)
           ( eq-is-contr'
             ( is-contr-map-is-equiv (is-equiv-postcomp-f X) f)
             ( pair ((pr1 sec-f) ∘ f) (ap (λ t → t ∘ f) (pr2 sec-f)))
             ( pair id refl))))

abstract
  is-equiv-postcomp-is-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) → is-equiv f →
    ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f))
  is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
    is-equiv-has-inverse 
      ( postcomp A (map-inv-is-equiv is-equiv-f))
      ( λ g → eq-htpy (htpy-right-whisk (issec-map-inv-is-equiv is-equiv-f) g))
      ( λ h → eq-htpy (htpy-right-whisk (isretr-map-inv-is-equiv is-equiv-f) h))

equiv-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X ≃ Y) → (A → X) ≃ (A → Y)
pr1 (equiv-postcomp A e) = postcomp A (map-equiv e)
pr2 (equiv-postcomp A e) =
  is-equiv-postcomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) A

is-emb-postcomp-is-emb :
  {l1 l2 l3 : Level} (A : UU l3) {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-emb f → is-emb (postcomp A f)
is-emb-postcomp-is-emb A f is-emb-f =
  is-emb-is-prop-map
    ( is-trunc-map-postcomp-is-trunc-map neg-one-𝕋 A f
      ( is-prop-map-is-emb is-emb-f))

is-emb-is-emb-postcomp :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
  ({l : Level} (A : UU l) → is-emb (postcomp A f)) → is-emb f
is-emb-is-emb-postcomp f is-emb-post-f =
  is-emb-is-prop-map
    ( is-trunc-map-is-trunc-map-postcomp neg-one-𝕋 f
      ( λ A → is-prop-map-is-emb (is-emb-post-f A)))

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

-- Exercise 13.13

-- Exercise 13.14

-- Exercise 13.15
    
-- Exercise 13.12

-- Exercise 13.15

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
