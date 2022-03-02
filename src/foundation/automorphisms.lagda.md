# Automorphisms of types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.automorphisms where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using
  ( is-contr; is-contr-total-path; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; map-equiv; map-inv-equiv; issec-map-inv-equiv; isretr-map-inv-equiv;
    is-equiv; map-inv-is-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using
  ( _~_; refl-htpy; is-contr-total-htpy; equiv-concat-htpy; right-unit-htpy)
open import foundation.identity-types using (Id; _∙_; ap; refl; right-unit)
open import foundation.structure-identity-principle using
  ( is-contr-total-Eq-structure)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Idea

An automorphism on a type `A` is an equivalence `A ≃ A`.

## Definitions

### The type of automorphisms on a type

```agda
Aut : {l1 : Level} → UU l1 → UU l1
Aut Y = Y ≃ Y
```

### Types equipped with an automorphism

```agda
UU-Pointed-Type-With-Aut :
  (l : Level) → UU (lsuc l)
UU-Pointed-Type-With-Aut l =
  Σ (UU l) (λ X → X × (X ≃ X))

type-Pointed-Type-With-Aut :
  {l : Level} → UU-Pointed-Type-With-Aut l → UU l
type-Pointed-Type-With-Aut X = pr1 X

point-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) → type-Pointed-Type-With-Aut X
point-Pointed-Type-With-Aut X = pr1 (pr2 X)

aut-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  type-Pointed-Type-With-Aut X ≃ type-Pointed-Type-With-Aut X
aut-Pointed-Type-With-Aut X = pr2 (pr2 X)

map-aut-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut X
map-aut-Pointed-Type-With-Aut X =
  map-equiv (aut-Pointed-Type-With-Aut X)

inv-map-aut-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut X
inv-map-aut-Pointed-Type-With-Aut X =
  map-inv-equiv (aut-Pointed-Type-With-Aut X)

issec-inv-map-aut-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  ((map-aut-Pointed-Type-With-Aut X) ∘ (inv-map-aut-Pointed-Type-With-Aut X))
  ~ id
issec-inv-map-aut-Pointed-Type-With-Aut X =
  issec-map-inv-equiv (aut-Pointed-Type-With-Aut X)

isretr-inv-map-aut-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  ((inv-map-aut-Pointed-Type-With-Aut X) ∘ (map-aut-Pointed-Type-With-Aut X))
  ~ id
isretr-inv-map-aut-Pointed-Type-With-Aut X =
  isretr-map-inv-equiv (aut-Pointed-Type-With-Aut X)
```

## Properties

```agda
-- We introduce the type of morphisms of pointed types with an automorphism

hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} →
  UU-Pointed-Type-With-Aut l1 → UU-Pointed-Type-With-Aut l2 → UU (l1 ⊔ l2)
hom-Pointed-Type-With-Aut {l1} {l2} X Y =
  Σ ( type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut Y)
    ( λ f →
      Id (f (point-Pointed-Type-With-Aut X)) (point-Pointed-Type-With-Aut Y)
      ×
      ( ( f ∘ (map-aut-Pointed-Type-With-Aut X)) ~
        ( (map-aut-Pointed-Type-With-Aut Y) ∘ f)))

-- Some trivial bureaucracy about morphisms of pointed types with an
-- automorphism

map-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) → hom-Pointed-Type-With-Aut X Y →
  type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut Y
map-hom-Pointed-Type-With-Aut X Y f = pr1 f

preserves-point-map-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (f : hom-Pointed-Type-With-Aut X Y) →
  Id ( map-hom-Pointed-Type-With-Aut X Y f (point-Pointed-Type-With-Aut X))
     ( point-Pointed-Type-With-Aut Y)
preserves-point-map-hom-Pointed-Type-With-Aut X Y f = pr1 (pr2 f)

preserves-aut-map-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (f : hom-Pointed-Type-With-Aut X Y) →
  ( ( map-hom-Pointed-Type-With-Aut X Y f) ∘ (map-aut-Pointed-Type-With-Aut X))
    ~
  ( ( map-aut-Pointed-Type-With-Aut Y) ∘ (map-hom-Pointed-Type-With-Aut X Y f))
preserves-aut-map-hom-Pointed-Type-With-Aut X Y f = pr2 (pr2 f)

-- We characterize the identity type of hom-Pointed-Type-With-Aut

htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  UU (l1 ⊔ l2)
htpy-hom-Pointed-Type-With-Aut X Y h1 h2 =
  Σ ( map-hom-Pointed-Type-With-Aut X Y h1
      ~ map-hom-Pointed-Type-With-Aut X Y h2)
    ( λ H →
      ( Id ( preserves-point-map-hom-Pointed-Type-With-Aut X Y h1)
           ( ( H (point-Pointed-Type-With-Aut X)) ∙
             ( preserves-point-map-hom-Pointed-Type-With-Aut X Y h2)))
      ×
      ( ( x : type-Pointed-Type-With-Aut X) →
        ( Id ( ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h1 x) ∙
               ( ap (map-aut-Pointed-Type-With-Aut Y) (H x)))
             ( ( H (map-aut-Pointed-Type-With-Aut X x)) ∙
               ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h2 x)))))

refl-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h : hom-Pointed-Type-With-Aut X Y) →
  htpy-hom-Pointed-Type-With-Aut X Y h h
refl-htpy-hom-Pointed-Type-With-Aut X Y h =
  pair refl-htpy (pair refl (λ x → right-unit))

htpy-hom-Pointed-Type-With-Aut-eq :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  Id h1 h2 → htpy-hom-Pointed-Type-With-Aut X Y h1 h2
htpy-hom-Pointed-Type-With-Aut-eq X Y h1 .h1 refl =
  refl-htpy-hom-Pointed-Type-With-Aut X Y h1

-- This is the meat of the characterization of the type of morphisms of pointed
-- types with an equivalence. The only hard part is feeding the families
-- explicitly to Agda over and over again, because Agda is apparently not that
-- good at figuring out what the correct family is.

is-contr-total-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h1 : hom-Pointed-Type-With-Aut X Y) →
  is-contr
    ( Σ ( hom-Pointed-Type-With-Aut X Y)
        ( htpy-hom-Pointed-Type-With-Aut X Y h1))
is-contr-total-htpy-hom-Pointed-Type-With-Aut X Y h1 =
  is-contr-total-Eq-structure
    ( λ ( map-h2 : type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut Y)
        ( str-h2 : ( Id ( map-h2 (point-Pointed-Type-With-Aut X))
                        ( point-Pointed-Type-With-Aut Y)) ×
                   ( ( x : type-Pointed-Type-With-Aut X) →
                     Id ( map-h2 (map-aut-Pointed-Type-With-Aut X x))
                        ( map-aut-Pointed-Type-With-Aut Y (map-h2 x))))
        ( H : map-hom-Pointed-Type-With-Aut X Y h1 ~ map-h2)
      → ( Id ( preserves-point-map-hom-Pointed-Type-With-Aut X Y h1)
             ( ( H (point-Pointed-Type-With-Aut X)) ∙
               ( pr1 str-h2)))
        ×
        ( ( x : type-Pointed-Type-With-Aut X) →
          ( Id ( ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h1 x) ∙
                 ( ap (map-aut-Pointed-Type-With-Aut Y) (H x)))
               ( ( H (map-aut-Pointed-Type-With-Aut X x)) ∙
                 ( pr2 str-h2 x)))))
    ( is-contr-total-htpy (map-hom-Pointed-Type-With-Aut X Y h1))
    ( pair (map-hom-Pointed-Type-With-Aut X Y h1) refl-htpy)
    ( is-contr-total-Eq-structure
      ( λ ( pt-h2 : Id ( map-hom-Pointed-Type-With-Aut X Y h1
                         ( point-Pointed-Type-With-Aut X))
                       ( point-Pointed-Type-With-Aut Y))
          ( aut-h2 : ( x : type-Pointed-Type-With-Aut X) →
                     Id ( map-hom-Pointed-Type-With-Aut X Y h1
                          ( map-aut-Pointed-Type-With-Aut X x))
                        ( map-aut-Pointed-Type-With-Aut Y
                          ( map-hom-Pointed-Type-With-Aut X Y h1 x)))
          ( α : Id ( preserves-point-map-hom-Pointed-Type-With-Aut X Y h1)
                   ( pt-h2))
        → ( ( x : type-Pointed-Type-With-Aut X) →
            Id ( ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h1 x) ∙
                 ( refl))
               ( aut-h2 x)))
      ( is-contr-total-path
        ( preserves-point-map-hom-Pointed-Type-With-Aut X Y h1))
      ( pair (preserves-point-map-hom-Pointed-Type-With-Aut X Y h1) refl)
      ( is-contr-equiv'
        ( Σ ( ( x : type-Pointed-Type-With-Aut X) →
              Id ( map-hom-Pointed-Type-With-Aut X Y h1
                   ( map-aut-Pointed-Type-With-Aut X x))
                 ( map-aut-Pointed-Type-With-Aut Y
                   ( map-hom-Pointed-Type-With-Aut X Y h1 x)))
            ( λ aut-h2 →
              ( x : type-Pointed-Type-With-Aut X) →
              Id ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h1 x)
                 ( aut-h2 x)))
        ( equiv-tot (equiv-concat-htpy right-unit-htpy))
        ( is-contr-total-htpy
          ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h1))))

-- We complete the characterization of the identity type of the type of
-- morphisms of types with a point and an automorphism

is-equiv-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  is-equiv (htpy-hom-Pointed-Type-With-Aut-eq X Y h1 h2)
is-equiv-htpy-hom-Pointed-Type-With-Aut X Y h1 =
  fundamental-theorem-id h1
    ( refl-htpy-hom-Pointed-Type-With-Aut X Y h1)
    ( is-contr-total-htpy-hom-Pointed-Type-With-Aut X Y h1)
    ( htpy-hom-Pointed-Type-With-Aut-eq X Y h1)

eq-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  htpy-hom-Pointed-Type-With-Aut X Y h1 h2 → Id h1 h2
eq-htpy-hom-Pointed-Type-With-Aut X Y h1 h2 =
  map-inv-is-equiv (is-equiv-htpy-hom-Pointed-Type-With-Aut X Y h1 h2)
```
