---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-foundations.18-set-quotients where

open import foundation public
open import elementary-number-theory public


-- Corollary 18.5.4

-- Proposition 18.5.5

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    unique-map-trunc-Set :
      is-contr
        ( Σ ( type-trunc-Set A → type-trunc-Set B)
            ( λ h → (h ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)))
    unique-map-trunc-Set =
      universal-property-trunc-Set A (trunc-Set B) (unit-trunc-Set ∘ f)

  map-trunc-Set :
    type-trunc-Set A → type-trunc-Set B
  map-trunc-Set =
    pr1 (center unique-map-trunc-Set)

  naturality-trunc-Set :
    (map-trunc-Set ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)
  naturality-trunc-Set =
    pr2 (center unique-map-trunc-Set)

  htpy-map-trunc-Set :
    (h : type-trunc-Set A → type-trunc-Set B) →
    (H : (h ∘ unit-trunc-Set) ~ (unit-trunc-Set ∘ f)) →
    map-trunc-Set ~ h
  htpy-map-trunc-Set h H =
    htpy-eq
      ( ap pr1
        ( eq-is-contr unique-map-trunc-Set
          { pair map-trunc-Set naturality-trunc-Set}
          { pair h H}))

map-id-trunc-Set :
  {l1 : Level} {A : UU l1} → map-trunc-Set (id {A = A}) ~ id
map-id-trunc-Set {l1} {A} =
  htpy-eq
    ( ap pr1
      ( eq-is-contr
        ( universal-property-trunc-Set A (trunc-Set A) unit-trunc-Set)
        { pair (map-trunc-Set id) (naturality-trunc-Set id)}
        { pair id refl-htpy}))

map-comp-trunc-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-trunc-Set (g ∘ f) ~ (map-trunc-Set g ∘ map-trunc-Set f)
map-comp-trunc-Set {A = A} {C = C} g f =
  htpy-eq
    ( ap pr1
      ( eq-is-contr
        ( universal-property-trunc-Set
          A
          (trunc-Set C)
          (unit-trunc-Set ∘ (g ∘ f)))
        { pair (map-trunc-Set (g ∘ f)) (naturality-trunc-Set (g ∘ f))}
        { pair ( map-trunc-Set g ∘ map-trunc-Set f)
               ( ( map-trunc-Set g ·l naturality-trunc-Set f) ∙h
                 ( naturality-trunc-Set g ·r f))}))

htpy-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  (f ~ g) → (map-trunc-Set f ~ map-trunc-Set g)
htpy-trunc-Set {B = B} {f = f} {g} H =
  map-inv-is-equiv
    ( dependent-universal-property-trunc-Set
      ( λ x →
        set-Prop
          ( Id-Prop (trunc-Set B) (map-trunc-Set f x) (map-trunc-Set g x))))
    ( λ a →
      ( naturality-trunc-Set f a) ∙
      ( ( ap unit-trunc-Set (H a)) ∙
        ( inv (naturality-trunc-Set g a))))

abstract
  is-equiv-map-trunc-Set :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-equiv (map-trunc-Set f)
  is-equiv-map-trunc-Set {f = f} H =
    pair
      ( pair
        ( map-trunc-Set (pr1 (pr1 H)))
        ( ( inv-htpy (map-comp-trunc-Set f (pr1 (pr1 H)))) ∙h
          ( ( htpy-trunc-Set (pr2 (pr1 H))) ∙h
            ( map-id-trunc-Set))))
      ( pair
        ( map-trunc-Set (pr1 (pr2 H)))
        ( ( inv-htpy (map-comp-trunc-Set (pr1 (pr2 H)) f)) ∙h
          ( ( htpy-trunc-Set (pr2 (pr2 H))) ∙h
            ( map-id-trunc-Set))))

equiv-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (type-trunc-Set A ≃ type-trunc-Set B)
equiv-trunc-Set e =
  pair
    ( map-trunc-Set (map-equiv e))
    ( is-equiv-map-trunc-Set (is-equiv-map-equiv e))

map-equiv-trunc-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → type-trunc-Set A → type-trunc-Set B
map-equiv-trunc-Set e = map-equiv (equiv-trunc-Set e)

--------------------------------------------------------------------------------

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    distributive-trunc-coprod-Set :
      is-contr
        ( Σ ( type-equiv-Set
              ( trunc-Set (coprod A B))
              ( coprod-Set (trunc-Set A) (trunc-Set B)))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-coprod unit-trunc-Set unit-trunc-Set)))
    distributive-trunc-coprod-Set =
      uniqueness-trunc-Set
        ( coprod-Set (trunc-Set A) (trunc-Set B))
        ( map-coprod unit-trunc-Set unit-trunc-Set)
        ( λ {l} C →
          is-equiv-right-factor'
            ( ev-inl-inr (λ x → type-Set C))
            ( precomp-Set (map-coprod unit-trunc-Set unit-trunc-Set) C)
            ( universal-property-coprod (type-Set C))
            ( is-equiv-comp'
              ( map-prod
                ( precomp-Set unit-trunc-Set C)
                ( precomp-Set unit-trunc-Set C))
              ( ev-inl-inr (λ x → type-Set C))
              ( universal-property-coprod (type-Set C))
              ( is-equiv-map-prod
                ( precomp-Set unit-trunc-Set C)
                ( precomp-Set unit-trunc-Set C)
                ( is-set-truncation-trunc-Set A C)
                ( is-set-truncation-trunc-Set B C))))

  equiv-distributive-trunc-coprod-Set :
    type-equiv-Set
      ( trunc-Set (coprod A B))
      ( coprod-Set (trunc-Set A) (trunc-Set B))
  equiv-distributive-trunc-coprod-Set =
    pr1 (center distributive-trunc-coprod-Set)

  map-equiv-distributive-trunc-coprod-Set :
    type-hom-Set
      ( trunc-Set (coprod A B))
      ( coprod-Set (trunc-Set A) (trunc-Set B))
  map-equiv-distributive-trunc-coprod-Set =
    map-equiv equiv-distributive-trunc-coprod-Set

  triangle-distributive-trunc-coprod-Set :
    ( map-equiv-distributive-trunc-coprod-Set ∘ unit-trunc-Set) ~
    ( map-coprod unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-coprod-Set =
    pr2 (center distributive-trunc-coprod-Set)

-- Set truncations of Σ-types

module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  abstract
    trunc-Σ-Set :
      is-contr
        ( Σ ( type-trunc-Set (Σ A B) ≃
              type-trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))))
    trunc-Σ-Set =
      uniqueness-trunc-Set
        ( trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
        ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))
        ( λ {l} C →
          is-equiv-right-factor'
            ( ev-pair)
            ( precomp-Set (unit-trunc-Set ∘ tot (λ x → unit-trunc-Set)) C)
            ( is-equiv-ev-pair)
            ( is-equiv-htpy-equiv
              ( ( equiv-map-Π
                  ( λ x → equiv-universal-property-trunc-Set (B x) C)) ∘e
                ( ( equiv-ev-pair) ∘e
                  ( equiv-universal-property-trunc-Set
                    ( Σ A (type-trunc-Set ∘ B)) C)))
              ( refl-htpy)))

  equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) ≃ type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  equiv-trunc-Σ-Set =
    pr1 (center trunc-Σ-Set)

  map-equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) → type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  map-equiv-trunc-Σ-Set =
    map-equiv equiv-trunc-Σ-Set

  square-trunc-Σ-Set :
    ( map-equiv-trunc-Σ-Set ∘ unit-trunc-Set) ~
    ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))
  square-trunc-Σ-Set =
    pr2 (center trunc-Σ-Set)

  htpy-map-equiv-trunc-Σ-Set :
    map-trunc-Set (tot (λ x → unit-trunc-Set)) ~ map-equiv-trunc-Σ-Set
  htpy-map-equiv-trunc-Σ-Set =
    htpy-map-trunc-Set
      ( tot (λ x → unit-trunc-Set))
      ( map-equiv-trunc-Σ-Set)
      ( square-trunc-Σ-Set)

  abstract
    is-equiv-map-trunc-tot-unit-trunc-Set :
      is-equiv (map-trunc-Set (tot (λ (x : A) → unit-trunc-Set {A = B x})))
    is-equiv-map-trunc-tot-unit-trunc-Set =
      is-equiv-htpy-equiv
        ( equiv-trunc-Σ-Set)
        ( htpy-map-equiv-trunc-Σ-Set)

-- trunc-Set distributes over products

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    distributive-trunc-prod-Set :
      is-contr
        ( Σ ( type-trunc-Set (A × B) ≃ ( type-trunc-Set A × type-trunc-Set B))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-prod unit-trunc-Set unit-trunc-Set)))
    distributive-trunc-prod-Set =
      uniqueness-trunc-Set
        ( prod-Set (trunc-Set A) (trunc-Set B))
        ( map-prod unit-trunc-Set unit-trunc-Set)
        ( λ {l} C →
          is-equiv-right-factor'
            ( ev-pair)
            ( precomp-Set (map-prod unit-trunc-Set unit-trunc-Set) C)
            ( is-equiv-ev-pair)
            ( is-equiv-htpy-equiv
              ( ( equiv-universal-property-trunc-Set A (Π-Set' B (λ y → C))) ∘e
                ( ( equiv-postcomp
                    ( type-trunc-Set A)
                    (equiv-universal-property-trunc-Set B C)) ∘e
                  ( equiv-ev-pair)))
              ( refl-htpy)))

  equiv-distributive-trunc-prod-Set :
    type-trunc-Set (A × B) ≃ ( type-trunc-Set A × type-trunc-Set B)
  equiv-distributive-trunc-prod-Set =
    pr1 (center distributive-trunc-prod-Set)

  map-equiv-distributive-trunc-prod-Set :
    type-trunc-Set (A × B) → type-trunc-Set A × type-trunc-Set B
  map-equiv-distributive-trunc-prod-Set =
    map-equiv equiv-distributive-trunc-prod-Set

  triangle-distributive-trunc-prod-Set :
    ( map-equiv-distributive-trunc-prod-Set ∘ unit-trunc-Set) ~
    ( map-prod unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-prod-Set =
    pr2 (center distributive-trunc-prod-Set)

-- trunc-Set distributes over Π indexed by Fin

abstract
  distributive-trunc-Π-Fin-Set :
    {l : Level} (k : ℕ) (A : Fin k → UU l) →
    is-contr
      ( Σ ( ( type-trunc-Set ((x : Fin k) → A x)) ≃
            ( (x : Fin k) → type-trunc-Set (A x)))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set))))
  distributive-trunc-Π-Fin-Set zero-ℕ A =
    uniqueness-trunc-Set
      ( Π-Set empty-Set (λ x → trunc-Set (A x)))
      ( map-Π (λ x → unit-trunc-Set))
      ( λ {l} B →
        is-equiv-precomp-is-equiv
          ( map-Π (λ x → unit-trunc-Set))
          ( is-equiv-is-contr
            ( map-Π (λ x → unit-trunc-Set))
            ( dependent-universal-property-empty' A)
            ( dependent-universal-property-empty' (type-trunc-Set ∘ A)))
          ( type-Set B))
  distributive-trunc-Π-Fin-Set (succ-ℕ k) A =
    uniqueness-trunc-Set
      ( Π-Set (Fin-Set (succ-ℕ k)) (λ x → trunc-Set (A x)))
      ( map-Π (λ x → unit-trunc-Set))
      ( λ {l} B →
        is-equiv-left-factor'
          ( precomp (map-Π (λ x → unit-trunc-Set)) (type-Set B))
          ( precomp (ev-Maybe {B = type-trunc-Set ∘ A}) (type-Set B))
          ( is-equiv-comp'
            ( precomp ev-Maybe (type-Set B))
            ( precomp
              ( map-prod (map-Π (λ x → unit-trunc-Set)) unit-trunc-Set)
              ( type-Set B))
            ( is-equiv-right-factor'
              ( ev-pair)
              ( precomp
                ( map-prod (map-Π (λ x → unit-trunc-Set)) unit-trunc-Set)
                ( type-Set B))
              ( is-equiv-ev-pair)
              ( is-equiv-htpy-equiv
                ( ( ( pair
                      ( precomp
                        ( (map-Π (λ x → unit-trunc-Set)))
                        ( A (inr star) → type-Set B))
                      ( is-set-truncation-is-equiv
                        ( Π-Set (Fin-Set k) (λ x → trunc-Set (A (inl x))))
                        ( map-Π (λ x → unit-trunc-Set))
                        { map-equiv
                          ( pr1
                            ( center
                              ( distributive-trunc-Π-Fin-Set k (A ∘ inl))))}
                        ( pr2
                          ( center (distributive-trunc-Π-Fin-Set k (A ∘ inl))))
                        ( is-equiv-map-equiv
                          ( pr1
                            ( center
                              ( distributive-trunc-Π-Fin-Set k (A ∘ inl)))))
                        ( Π-Set' (A (inr star)) (λ a → B)))) ∘e
                    ( equiv-postcomp
                      ( (x : Fin k) → type-trunc-Set (A (inl x)))
                      ( equiv-universal-property-trunc-Set
                        ( A (inr star))
                        ( B)))) ∘e
                  ( equiv-ev-pair))
                ( refl-htpy)))
            ( is-equiv-precomp-is-equiv
              ( ev-Maybe)
              ( dependent-universal-property-Maybe)
              ( type-Set B)))
          ( is-equiv-precomp-is-equiv
            ( ev-Maybe)
            ( dependent-universal-property-Maybe)
            ( type-Set B)))

module _
  {l : Level} (k : ℕ) (A : Fin k → UU l)
  where

  equiv-distributive-trunc-Π-Fin-Set :
    type-trunc-Set ((x : Fin k) → A x) ≃ ((x : Fin k) → type-trunc-Set (A x))
  equiv-distributive-trunc-Π-Fin-Set =
    pr1 (center (distributive-trunc-Π-Fin-Set k A))

  map-equiv-distributive-trunc-Π-Fin-Set :
    type-trunc-Set ((x : Fin k) → A x) → ((x : Fin k) → type-trunc-Set (A x))
  map-equiv-distributive-trunc-Π-Fin-Set =
    map-equiv equiv-distributive-trunc-Π-Fin-Set

  triangle-distributive-trunc-Π-Fin-Set :
    ( map-equiv-distributive-trunc-Π-Fin-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-Fin-Set =
    pr2 (center (distributive-trunc-Π-Fin-Set k A))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  abstract
    distributive-trunc-Π-count-Set :
      count A → 
      is-contr
        ( Σ ( ( type-trunc-Set ((x : A) → B x)) ≃
              ( (x : A) → type-trunc-Set (B x)))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-Π (λ x → unit-trunc-Set))))
    distributive-trunc-Π-count-Set (pair k e) =
      is-contr-equiv
        ( Σ ( ( type-trunc-Set ((x : A) → B x)) ≃
              ( (x : Fin k) → type-trunc-Set (B (map-equiv e x))))
            ( λ f →
              ( map-equiv f ∘ unit-trunc-Set) ~
              ( map-Π (λ x → unit-trunc-Set) ∘ precomp-Π (map-equiv e) B)))
        ( equiv-Σ
          ( λ f →
            ( map-equiv f ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set) ∘ precomp-Π (map-equiv e) B))
          ( equiv-postcomp-equiv
            ( equiv-precomp-Π e (type-trunc-Set ∘ B))
            ( type-trunc-Set ((x : A) → B x)))
          ( λ f →
            equiv-map-Π
              ( λ h →
                ( ( inv-equiv equiv-funext) ∘e
                  ( equiv-precomp-Π e
                    ( λ x → Id ((map-equiv f ∘ unit-trunc-Set) h x)
                    ( map-Π (λ y → unit-trunc-Set) h x)))) ∘e
                ( equiv-funext))))
        ( is-contr-equiv'
          ( Σ ( ( type-trunc-Set ((x : Fin k) → B (map-equiv e x))) ≃
                ( (x : Fin k) → type-trunc-Set (B (map-equiv e x))))
              ( λ f →
                ( map-equiv f ∘ unit-trunc-Set) ~
                ( map-Π (λ x → unit-trunc-Set))))
          ( equiv-Σ
            ( λ f →
              ( map-equiv f ∘ unit-trunc-Set) ~
              ( map-Π (λ x → unit-trunc-Set) ∘ precomp-Π (map-equiv e) B))
            ( equiv-precomp-equiv
              ( equiv-trunc-Set (equiv-precomp-Π e B))
              ( (x : Fin k) → type-trunc-Set (B (map-equiv e x))))
            ( λ f →
              equiv-Π
                ( λ h →
                  Id ( map-equiv f
                       ( map-equiv
                         ( equiv-trunc-Set (equiv-precomp-Π e B))
                         ( unit-trunc-Set h)))
                     ( map-Π (λ x → unit-trunc-Set) (λ x → h (map-equiv e x))))
                ( equiv-Π B e (λ x → id-equiv))
                ( λ h →
                  ( ( inv-equiv equiv-funext) ∘e
                    ( equiv-Π
                      ( λ x →
                        Id ( map-equiv f
                             ( map-equiv-trunc-Set
                               ( equiv-precomp-Π e B)
                               ( unit-trunc-Set
                                 ( map-equiv-Π B e (λ x → id-equiv) h)))
                             ( x))
                           ( unit-trunc-Set
                             ( map-equiv-Π B e
                               ( λ z → id-equiv)
                               ( h)
                               ( map-equiv e x))))
                      ( id-equiv)
                      ( λ x →
                        ( equiv-concat
                          ( ap
                            ( λ t → map-equiv f t x)
                            ( ( naturality-trunc-Set (precomp-Π (map-equiv e) B)
                                ( map-equiv-Π B e (λ _ → id-equiv) h)) ∙
                              ( ap
                                ( unit-trunc-Set)
                                ( eq-htpy
                                  ( compute-map-equiv-Π B e
                                    ( λ _ → id-equiv)
                                    ( h))))))
                          ( unit-trunc-Set
                            ( map-equiv-Π B e
                              ( λ _ → id-equiv)
                              ( h)
                              ( map-equiv e x)))) ∘e
                        ( equiv-concat'
                          ( map-equiv f (unit-trunc-Set h) x)
                          ( ap unit-trunc-Set
                            ( inv
                              ( compute-map-equiv-Π B e
                                ( λ _ → id-equiv)
                                ( h)
                                ( x)))))))) ∘e
                  ( equiv-funext))))
          ( distributive-trunc-Π-Fin-Set k (B ∘ map-equiv e)))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (c : count A)
  where

  equiv-distributive-trunc-Π-count-Set :
    ( type-trunc-Set ((x : A) → B x)) ≃ ((x : A) → type-trunc-Set (B x))
  equiv-distributive-trunc-Π-count-Set =
    pr1 (center (distributive-trunc-Π-count-Set B c))

  map-equiv-distributive-trunc-Π-count-Set :
    ( type-trunc-Set ((x : A) → B x)) → ((x : A) → type-trunc-Set (B x))
  map-equiv-distributive-trunc-Π-count-Set =
    map-equiv equiv-distributive-trunc-Π-count-Set

  triangle-distributive-trunc-Π-count-Set :
    ( map-equiv-distributive-trunc-Π-count-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-count-Set =
    pr2 (center (distributive-trunc-Π-count-Set B c))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (H : is-finite A)
  where

  abstract
    distributive-trunc-Π-is-finite-Set :
      is-contr
        ( Σ ( ( type-trunc-Set ((x : A) → B x)) ≃
              ( (x : A) → type-trunc-Set (B x)))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-Π (λ x → unit-trunc-Set))))
    distributive-trunc-Π-is-finite-Set =
      apply-universal-property-trunc-Prop H
        ( is-contr-Prop _)
        ( distributive-trunc-Π-count-Set B)

  equiv-distributive-trunc-Π-is-finite-Set :
    ( type-trunc-Set ((x : A) → B x)) ≃ ((x : A) → type-trunc-Set (B x))
  equiv-distributive-trunc-Π-is-finite-Set =
    pr1 (center distributive-trunc-Π-is-finite-Set)

  map-equiv-distributive-trunc-Π-is-finite-Set :
    ( type-trunc-Set ((x : A) → B x)) → ((x : A) → type-trunc-Set (B x))
  map-equiv-distributive-trunc-Π-is-finite-Set =
    map-equiv equiv-distributive-trunc-Π-is-finite-Set

  triangle-distributive-trunc-Π-is-finite-Set :
    ( map-equiv-distributive-trunc-Π-is-finite-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-is-finite-Set =
    pr2 (center distributive-trunc-Π-is-finite-Set)

--------------------------------------------------------------------------------

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where
    
  is-choice-of-representatives :
    (A → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-choice-of-representatives P =
    (a : A) → is-contr (Σ A (λ x → P x × type-Eq-Rel R a x))
  
  representatives :
    {P : A → UU l3} → is-choice-of-representatives P → UU (l1 ⊔ l3)
  representatives {P} H = Σ A P
  
  quotient-map-large-set-quotient-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    representatives H → large-set-quotient R
  quotient-map-large-set-quotient-representatives H a =
    quotient-map-large-set-quotient R (pr1 a)

  abstract
    is-surjective-quotient-map-large-set-quotient-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives P) →
      is-surjective (quotient-map-large-set-quotient-representatives H)
    is-surjective-quotient-map-large-set-quotient-representatives H (pair Q K) =
      apply-universal-property-trunc-Prop K
        ( trunc-Prop
          ( fib (quotient-map-large-set-quotient-representatives H) (pair Q K)))
        ( λ { (pair a refl) →
              unit-trunc-Prop
                ( pair
                  ( pair (pr1 (center (H a))) (pr1 (pr2 (center (H a)))))
                  ( ( apply-effectiveness-quotient-map-large-set-quotient' R
                      ( symm-Eq-Rel R (pr2 (pr2 (center (H a)))))) ∙
                    ( ap
                      ( pair (prop-Eq-Rel R a))
                      ( eq-is-prop is-prop-type-trunc-Prop))))})

  abstract
    is-emb-quotient-map-large-set-quotient-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives P) →
      is-emb (quotient-map-large-set-quotient-representatives H)
    is-emb-quotient-map-large-set-quotient-representatives {P} H (pair a p) =
      fundamental-theorem-id
        ( pair a p)
        ( refl)
        ( is-contr-equiv
          ( Σ A (λ x → P x × type-Eq-Rel R a x))
          ( ( assoc-Σ A P (λ z → type-Eq-Rel R a (pr1 z))) ∘e
            ( equiv-tot
              ( λ t →
                is-effective-quotient-map-large-set-quotient R a (pr1 t))))
          ( H a))
        ( λ y →
          ap (quotient-map-large-set-quotient-representatives H) {pair a p} {y})

  abstract
    is-equiv-quotient-map-large-set-quotient-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives P) →
      is-equiv (quotient-map-large-set-quotient-representatives H)
    is-equiv-quotient-map-large-set-quotient-representatives H =
      is-equiv-is-emb-is-surjective
        ( is-surjective-quotient-map-large-set-quotient-representatives H)
        ( is-emb-quotient-map-large-set-quotient-representatives H)

  equiv-large-set-quotient-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives P) →
    representatives H ≃ large-set-quotient R
  equiv-large-set-quotient-representatives H =
    pair ( quotient-map-large-set-quotient-representatives H)
         ( is-equiv-quotient-map-large-set-quotient-representatives H)

-- We construct ℚ by unique representatives of sim-pre-ℚ

is-relative-prime-ℤ : ℤ → ℤ → UU lzero
is-relative-prime-ℤ x y = is-one-ℤ (gcd-ℤ x y)

is-reduced-pre-ℚ : pre-ℚ → UU lzero
is-reduced-pre-ℚ x =
  is-relative-prime-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x)

ℚ : UU lzero
ℚ = Σ pre-ℚ is-reduced-pre-ℚ

reduce-numerator-pre-ℚ :
  (x : pre-ℚ) →
  div-ℤ (gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x)) (numerator-pre-ℚ x)
reduce-numerator-pre-ℚ x =
  pr1 (is-common-divisor-gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x))

int-reduce-numerator-pre-ℚ : pre-ℚ → ℤ
int-reduce-numerator-pre-ℚ x = pr1 (reduce-numerator-pre-ℚ x)

eq-reduce-numerator-pre-ℚ :
  (x : pre-ℚ) →
  Id ( mul-ℤ
       ( int-reduce-numerator-pre-ℚ x)
       ( gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x)))
     ( numerator-pre-ℚ x)
eq-reduce-numerator-pre-ℚ x = pr2 (reduce-numerator-pre-ℚ x)

reduce-denominator-pre-ℚ :
  (x : pre-ℚ) →
  div-ℤ (gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x)) (denominator-pre-ℚ x)
reduce-denominator-pre-ℚ x =
  pr2 (is-common-divisor-gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x))

int-reduce-denominator-pre-ℚ : pre-ℚ → ℤ
int-reduce-denominator-pre-ℚ x =
  pr1 (reduce-denominator-pre-ℚ x)

eq-reduce-denominator-pre-ℚ :
  (x : pre-ℚ) →
  Id ( mul-ℤ
       ( int-reduce-denominator-pre-ℚ x)
       ( gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x)))
     ( denominator-pre-ℚ x)
eq-reduce-denominator-pre-ℚ x =
  pr2 (reduce-denominator-pre-ℚ x)

is-positive-int-reduce-denominator-pre-ℚ :
  (x : pre-ℚ) → is-positive-ℤ (int-reduce-denominator-pre-ℚ x)
is-positive-int-reduce-denominator-pre-ℚ x =
  is-positive-left-factor-mul-ℤ
    ( is-positive-eq-ℤ
      ( inv (eq-reduce-denominator-pre-ℚ x))
      ( is-positive-denominator-pre-ℚ x))
    ( is-positive-gcd-is-positive-right-ℤ
      ( numerator-pre-ℚ x)
      ( denominator-pre-ℚ x)
      ( is-positive-denominator-pre-ℚ x))

reduce-pre-ℚ : pre-ℚ → pre-ℚ
reduce-pre-ℚ x =
  pair
    ( int-reduce-numerator-pre-ℚ x)
    ( pair
      ( int-reduce-denominator-pre-ℚ x)
      ( is-positive-int-reduce-denominator-pre-ℚ x))

{-
is-reduced-reduce-pre-ℚ :
  (x : pre-ℚ) → is-reduced-pre-ℚ (reduce-pre-ℚ x)
is-reduced-reduce-pre-ℚ x = {!!}
-}

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 18.17

has-finite-components-Prop : {l : Level} → UU l → UU-Prop l
has-finite-components-Prop A = is-finite-Prop (type-trunc-Set A)

has-finite-components : {l : Level} → UU l → UU l
has-finite-components A = type-Prop (has-finite-components-Prop A)

has-cardinality-components-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
has-cardinality-components-Prop k A =
  has-cardinality-Prop (type-trunc-Set A) k

has-cardinality-components : {l : Level} (k : ℕ) → UU l → UU l
has-cardinality-components k A =
  type-Prop (has-cardinality-components-Prop k A)

has-set-presentation-Prop :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU l2) → UU-Prop (l1 ⊔ l2)
has-set-presentation-Prop A B =
  ∃-Prop (λ (f : type-Set A → B) → is-equiv (unit-trunc-Set ∘ f))

has-finite-presentation-Prop :
  {l1 : Level} (k : ℕ) (A : UU l1) → UU-Prop l1
has-finite-presentation-Prop k A =
  has-set-presentation-Prop (Fin-Set k) A

has-finite-presentation :
  {l1 : Level} (k : ℕ) (A : UU l1) → UU l1
has-finite-presentation k A = type-Prop (has-finite-presentation-Prop k A)
  
has-finite-presentation-has-cardinality-components :
  {l : Level} {k : ℕ} {A : UU l} → has-cardinality-components k A →
  has-finite-presentation k A
has-finite-presentation-has-cardinality-components {l} {k} {A} H =
  apply-universal-property-trunc-Prop H
    ( has-finite-presentation-Prop k A)
    ( λ e →
      apply-universal-property-trunc-Prop
        ( P2 e)
        ( has-finite-presentation-Prop k A)
        ( λ g →
          unit-trunc-Prop
            ( pair
              ( λ x → pr1 (g x))
              ( is-equiv-htpy-equiv e (λ x → pr2 (g x))))))
  where
  P1 : (e : Fin k ≃ type-trunc-Set A) (x : Fin k) →
       type-trunc-Prop (fib unit-trunc-Set (map-equiv e x))
  P1 e x = is-surjective-unit-trunc-Set A (map-equiv e x)
  P2 : (e : Fin k ≃ type-trunc-Set A) →
       type-trunc-Prop ((x : Fin k) → fib unit-trunc-Set (map-equiv e x))
  P2 e = finite-choice-Fin (P1 e)

has-cardinality-components-has-finite-presentation :
  {l : Level} {k : ℕ} {A : UU l} → has-finite-presentation k A →
  has-cardinality-components k A
has-cardinality-components-has-finite-presentation {l} {k} {A} H =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-components-Prop k A)
    ( λ { (pair f E) → unit-trunc-Prop (pair (unit-trunc-Set ∘ f) E)})

-- Exercise 18.18

is-path-connected-Prop : {l : Level} → UU l → UU-Prop l
is-path-connected-Prop A = is-contr-Prop (type-trunc-Set A)

is-path-connected : {l : Level} → UU l → UU l
is-path-connected A = type-Prop (is-path-connected-Prop A)

abstract
  is-inhabited-is-path-connected :
    {l : Level} {A : UU l} → is-path-connected A → type-trunc-Prop A
  is-inhabited-is-path-connected {l} {A} C =
    apply-universal-property-trunc-Set
      ( center C)
      ( set-Prop (trunc-Prop A))
      ( unit-trunc-Prop)

abstract
  mere-eq-is-path-connected :
    {l : Level} {A : UU l} → is-path-connected A → (x y : A) → mere-eq x y
  mere-eq-is-path-connected {A = A} H x y =
    apply-effectiveness-unit-trunc-Set (eq-is-contr H)

abstract
  is-path-connected-mere-eq :
    {l : Level} {A : UU l} (a : A) →
    ((x : A) → mere-eq a x) → is-path-connected A
  is-path-connected-mere-eq {l} {A} a e =
    pair
      ( unit-trunc-Set a)
      ( apply-dependent-universal-property-trunc-Set
        ( λ x → set-Prop (Id-Prop (trunc-Set A) (unit-trunc-Set a) x))
        ( λ x → apply-effectiveness-unit-trunc-Set' (e x)))

is-path-connected-is-surjective-pt :
  {l1 : Level} {A : UU l1} (a : A) →
  is-surjective (pt a) → is-path-connected A
is-path-connected-is-surjective-pt a H =
  is-path-connected-mere-eq a
    ( λ x →
      apply-universal-property-trunc-Prop
        ( H x)
        ( mere-eq-Prop a x)
        ( λ u → unit-trunc-Prop (pr2 u)))

is-surjective-pt-is-path-connected :
  {l1 : Level} {A : UU l1} (a : A) →
  is-path-connected A → is-surjective (pt a)
is-surjective-pt-is-path-connected a H x =
  apply-universal-property-trunc-Prop
    ( mere-eq-is-path-connected H a x)
    ( trunc-Prop (fib (pt a) x))
    ( λ {refl → unit-trunc-Prop (pair star refl)})

equiv-dependent-universal-property-is-path-connected :
  {l1 : Level} {A : UU l1} (a : A) → is-path-connected A →
  ( {l : Level} (P : A → UU-Prop l) →
    ((x : A) → type-Prop (P x)) ≃ type-Prop (P a))
equiv-dependent-universal-property-is-path-connected a H P =
  ( equiv-universal-property-unit (type-Prop (P a))) ∘e
  ( equiv-dependent-universal-property-surj-is-surjective
    ( pt a)
    ( is-surjective-pt-is-path-connected a H)
    ( P))

apply-dependent-universal-property-is-path-connected :
  {l1 : Level} {A : UU l1} (a : A) → is-path-connected A →
  {l : Level} (P : A → UU-Prop l) → type-Prop (P a) → (x : A) → type-Prop (P x)
apply-dependent-universal-property-is-path-connected a H P =
  map-inv-equiv (equiv-dependent-universal-property-is-path-connected a H P)

abstract
  is-surjective-fiber-inclusion :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-path-connected A → (a : A) → is-surjective (fiber-inclusion B a)
  is-surjective-fiber-inclusion {B = B} C a (pair x b) =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-path-connected C a x)
      ( trunc-Prop (fib (fiber-inclusion B a) (pair x b)))
      ( λ { refl → unit-trunc-Prop (pair b refl)})

abstract
  mere-eq-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    (x : A) → mere-eq a x
  mere-eq-is-surjective-fiber-inclusion a H x =
    apply-universal-property-trunc-Prop
      ( H (λ x → unit) (pair x star))
      ( mere-eq-Prop a x)
      ( λ u → unit-trunc-Prop (ap pr1 (pr2 u)))

abstract
  is-path-connected-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    is-path-connected A
  is-path-connected-is-surjective-fiber-inclusion a H =
    is-path-connected-mere-eq a (mere-eq-is-surjective-fiber-inclusion a H)

-- Bureaucracy

abstract
  mere-eq-mere-equiv :
    {l : Level} {A B : UU l} → mere-equiv A B → mere-eq A B
  mere-eq-mere-equiv {l} {A} {B} = functor-trunc-Prop (eq-equiv A B)

abstract
  is-path-connected-component-UU :
    {l : Level} (X : UU l) → is-path-connected (component-UU X)
  is-path-connected-component-UU X =
    is-path-connected-mere-eq
      ( pair X (refl-mere-equiv X))
      ( λ Y →
        functor-trunc-Prop
          ( eq-equiv-component-UU (pair X (refl-mere-equiv X)) Y)
          ( mere-equiv-component-UU Y))

abstract
  is-path-connected-UU-Fin-Level :
    {l : Level} (n : ℕ) → is-path-connected (UU-Fin-Level l n)
  is-path-connected-UU-Fin-Level {l} n =
    is-path-connected-mere-eq
      ( Fin-UU-Fin-Level l n)
      ( λ A →
        functor-trunc-Prop
          ( ( eq-equiv-UU-Fin-Level (Fin-UU-Fin-Level l n) A) ∘
            ( map-equiv
              ( equiv-precomp-equiv
                ( inv-equiv (equiv-raise l (Fin n)))
                ( type-UU-Fin-Level A))))
          ( pr2 A))

abstract
  is-path-connected-UU-Fin :
    (n : ℕ) → is-path-connected (UU-Fin n)
  is-path-connected-UU-Fin n =
    is-path-connected-mere-eq
      ( Fin-UU-Fin n)
      ( λ A → functor-trunc-Prop (eq-equiv-UU-Fin (Fin-UU-Fin n) A) (pr2 A)) 

-- Exercise 18.19

-- Exercise 18.19 (a)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-injective-map-trunc-Set :
      is-injective f → is-injective (map-trunc-Set f)
    is-injective-map-trunc-Set H {x} {y} =
      apply-dependent-universal-property-trunc-Set
        ( λ u →
          set-Prop
            ( function-Prop (Id (map-trunc-Set f u) (map-trunc-Set f y))
            ( Id-Prop (trunc-Set A) u y) ))
        ( λ a →
          apply-dependent-universal-property-trunc-Set
          ( λ v →
            set-Prop
              ( function-Prop
                ( Id (map-trunc-Set f (unit-trunc-Set a)) (map-trunc-Set f v))
                ( Id-Prop (trunc-Set A) (unit-trunc-Set a) v)))
          ( λ b p →
            apply-universal-property-trunc-Prop
              ( apply-effectiveness-unit-trunc-Set
                ( ( inv (naturality-trunc-Set f a)) ∙
                  ( p ∙ (naturality-trunc-Set f b))))
              ( Id-Prop (trunc-Set A) (unit-trunc-Set a) (unit-trunc-Set b))
              ( λ q → ap unit-trunc-Set (H q)))
          ( y))
        ( x)

-- Exercise 18.19 (b)

  abstract
    is-surjective-map-trunc-Set :
      is-surjective f → is-surjective (map-trunc-Set f)
    is-surjective-map-trunc-Set H =
      apply-dependent-universal-property-trunc-Set
        ( λ x → set-Prop (trunc-Prop (fib (map-trunc-Set f) x)))
        ( λ b →
          apply-universal-property-trunc-Prop
            ( H b)
            ( trunc-Prop (fib (map-trunc-Set f) (unit-trunc-Set b)))
            ( λ { (pair a p) →
                  unit-trunc-Prop
                    ( pair
                      ( unit-trunc-Set a)
                      ( naturality-trunc-Set f a ∙ ap unit-trunc-Set p))}))

  abstract
    is-surjective-is-surjective-map-trunc-Set :
      is-surjective (map-trunc-Set f) → is-surjective f
    is-surjective-is-surjective-map-trunc-Set H b =
      apply-universal-property-trunc-Prop
        ( H (unit-trunc-Set b))
        ( trunc-Prop (fib f b))
        ( λ { (pair x p) →
              apply-universal-property-trunc-Prop
                ( is-surjective-unit-trunc-Set A x)
                ( trunc-Prop (fib f b))
                ( λ { (pair a refl) →
                      apply-universal-property-trunc-Prop
                        ( apply-effectiveness-unit-trunc-Set
                          ( inv (naturality-trunc-Set f a) ∙ p))
                        ( trunc-Prop (fib f b))
                        ( λ q → unit-trunc-Prop (pair a q))})})

  -- Exercise 18.19 (c)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  inclusion-trunc-im-Set : type-trunc-Set (im f) → type-trunc-Set B
  inclusion-trunc-im-Set = map-trunc-Set (inclusion-im f)

  abstract
    is-emb-inclusion-trunc-im-Set : is-emb inclusion-trunc-im-Set
    is-emb-inclusion-trunc-im-Set =
      is-emb-is-injective
        ( is-set-type-trunc-Set)
        ( is-injective-map-trunc-Set
          ( inclusion-im f)
          ( is-injective-is-emb (is-emb-inclusion-im f)))

  emb-trunc-im-Set : type-trunc-Set (im f) ↪ type-trunc-Set B
  emb-trunc-im-Set = pair inclusion-trunc-im-Set is-emb-inclusion-trunc-im-Set

  abstract
    is-injective-inclusion-trunc-im-Set : is-injective inclusion-trunc-im-Set
    is-injective-inclusion-trunc-im-Set =
      is-injective-is-emb is-emb-inclusion-trunc-im-Set

  map-hom-slice-trunc-im-Set : type-trunc-Set A → type-trunc-Set (im f)
  map-hom-slice-trunc-im-Set = map-trunc-Set (map-unit-im f)

  triangle-hom-slice-trunc-im-Set :
    map-trunc-Set f ~ (inclusion-trunc-im-Set ∘ map-trunc-Set (map-unit-im f))
  triangle-hom-slice-trunc-im-Set =
    ( htpy-trunc-Set (triangle-unit-im f)) ∙h
    ( map-comp-trunc-Set (inclusion-im f) (map-unit-im f))

  hom-slice-trunc-im-Set : hom-slice (map-trunc-Set f) inclusion-trunc-im-Set
  hom-slice-trunc-im-Set =
    pair map-hom-slice-trunc-im-Set triangle-hom-slice-trunc-im-Set

  abstract
    is-surjective-map-hom-slice-trunc-im-Set :
      is-surjective map-hom-slice-trunc-im-Set
    is-surjective-map-hom-slice-trunc-im-Set =
      is-surjective-map-trunc-Set
        ( map-unit-im f)
        ( is-surjective-map-unit-im f)

  abstract
    is-image-trunc-im-Set :
      {l : Level} →
      is-image l
        ( map-trunc-Set f)
        ( emb-trunc-im-Set)
        ( hom-slice-trunc-im-Set)
    is-image-trunc-im-Set =
      is-image-is-surjective
        ( map-trunc-Set f)
        ( emb-trunc-im-Set)
        ( hom-slice-trunc-im-Set)
        ( is-surjective-map-hom-slice-trunc-im-Set)

  abstract
    unique-equiv-trunc-im-Set :
      is-contr
        ( Σ ( equiv-slice
              ( inclusion-im (map-trunc-Set f))
              ( inclusion-trunc-im-Set))
            ( λ e →
              htpy-hom-slice (map-trunc-Set f)
                ( inclusion-trunc-im-Set)
                ( comp-hom-slice (map-trunc-Set f)
                  ( inclusion-im (map-trunc-Set f))
                  ( inclusion-trunc-im-Set)
                  ( hom-equiv-slice
                    ( inclusion-im (map-trunc-Set f))
                    ( inclusion-trunc-im-Set)
                    ( e))
                  ( unit-im (map-trunc-Set f)))
                ( hom-slice-trunc-im-Set)))
    unique-equiv-trunc-im-Set =
      uniqueness-im
        ( map-trunc-Set f)
        ( emb-trunc-im-Set)
        ( hom-slice-trunc-im-Set)
        ( is-image-trunc-im-Set)

  equiv-slice-trunc-im-Set :
    equiv-slice (inclusion-im (map-trunc-Set f)) inclusion-trunc-im-Set
  equiv-slice-trunc-im-Set = pr1 (center unique-equiv-trunc-im-Set)

  equiv-trunc-im-Set : im (map-trunc-Set f) ≃ type-trunc-Set (im f)
  equiv-trunc-im-Set = pr1 equiv-slice-trunc-im-Set

  map-equiv-trunc-im-Set : im (map-trunc-Set f) → type-trunc-Set (im f)
  map-equiv-trunc-im-Set = map-equiv equiv-trunc-im-Set

  triangle-trunc-im-Set :
    ( inclusion-im (map-trunc-Set f)) ~
    ( inclusion-trunc-im-Set ∘ map-equiv-trunc-im-Set)
  triangle-trunc-im-Set = pr2 equiv-slice-trunc-im-Set

  htpy-hom-slice-trunc-im-Set :
    htpy-hom-slice
      ( map-trunc-Set f)
      ( inclusion-trunc-im-Set)
      ( comp-hom-slice
        ( map-trunc-Set f)
        ( inclusion-im (map-trunc-Set f))
        ( inclusion-trunc-im-Set)
        ( hom-equiv-slice
          ( inclusion-im (map-trunc-Set f))
          ( inclusion-trunc-im-Set)
          ( equiv-slice-trunc-im-Set))
        ( unit-im (map-trunc-Set f)))
      ( hom-slice-trunc-im-Set)
  htpy-hom-slice-trunc-im-Set =
    pr2 (center unique-equiv-trunc-im-Set)

  htpy-map-hom-slice-trunc-im-Set :
    ( map-equiv-trunc-im-Set ∘ (map-unit-im (map-trunc-Set f))) ~
    ( map-hom-slice-trunc-im-Set)
  htpy-map-hom-slice-trunc-im-Set =
    pr1 htpy-hom-slice-trunc-im-Set

  tetrahedron-map-hom-slice-trunc-im-Set :
    ( ( triangle-trunc-im-Set ·r map-unit-im (map-trunc-Set f)) ∙h
      ( inclusion-trunc-im-Set ·l htpy-map-hom-slice-trunc-im-Set)) ~
    ( triangle-hom-slice-trunc-im-Set)
  tetrahedron-map-hom-slice-trunc-im-Set =
    pr2 htpy-hom-slice-trunc-im-Set

  unit-im-map-trunc-Set :
    im f → im (map-trunc-Set f)
  unit-im-map-trunc-Set x =
    pair
      ( unit-trunc-Set (pr1 x))
      ( apply-universal-property-trunc-Prop (pr2 x)
        ( trunc-Prop (fib (map-trunc-Set f) (unit-trunc-Set (pr1 x))))
        ( λ u →
          unit-trunc-Prop
            ( pair
              ( unit-trunc-Set (pr1 u))
              ( naturality-trunc-Set f (pr1 u) ∙ ap unit-trunc-Set (pr2 u)))))

  left-square-unit-im-map-trunc-Set :
    ( map-unit-im (map-trunc-Set f) ∘ unit-trunc-Set) ~
    ( unit-im-map-trunc-Set ∘ map-unit-im f)
  left-square-unit-im-map-trunc-Set a =
    eq-Eq-im
      ( map-trunc-Set f)
      ( map-unit-im (map-trunc-Set f) (unit-trunc-Set a))
      ( unit-im-map-trunc-Set (map-unit-im f a))
      ( naturality-trunc-Set f a)

  right-square-unit-im-map-trunc-Set :
    ( inclusion-im (map-trunc-Set f) ∘ unit-im-map-trunc-Set) ~
    ( unit-trunc-Set ∘ inclusion-im f)
  right-square-unit-im-map-trunc-Set x = refl

  abstract
    is-set-truncation-im-map-trunc-Set :
      {l : Level} →
      is-set-truncation l
        ( im-Set (trunc-Set B) (map-trunc-Set f))
        ( unit-im-map-trunc-Set)
    is-set-truncation-im-map-trunc-Set =
      is-set-truncation-is-equiv-is-set-truncation
        ( im-Set (trunc-Set B) (map-trunc-Set f))
        ( unit-im-map-trunc-Set)
        ( trunc-Set (im f))
        ( unit-trunc-Set)
        ( λ b →
          is-injective-inclusion-trunc-im-Set
            ( ( inv (triangle-trunc-im-Set (unit-im-map-trunc-Set b))) ∙
              ( inv (naturality-trunc-Set (inclusion-im f) b))))
        ( is-set-truncation-trunc-Set (im f))
        ( is-equiv-map-equiv equiv-trunc-im-Set)
```
