---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-foundations.18-set-quotients where

open import foundation public
open import elementary-number-theory public

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

-- We construct ℚ by unique representatives of sim-pre-ℚ

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 18.17

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
