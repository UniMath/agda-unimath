---
title: Algebras for polynomial endofunctors
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module foundation.algebras-polynomial-endofunctors where

open import foundation.contractible-types using (is-contr; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  (_∘e_; is-equiv; map-inv-is-equiv; _≃_)
open import foundation.functions using (_∘_)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using
  ( _~_; _∙h_; _·l_; _·r_; refl-htpy; is-contr-total-htpy; equiv-concat-htpy;
    right-unit-htpy)
open import foundation.identity-types using
  ( ap; concat; _∙_; right-unit; _＝_; refl)
open import foundation.polynomial-endofunctors using
  ( type-polynomial-endofunctor; map-polynomial-endofunctor;
    htpy-polynomial-endofunctor; coh-refl-htpy-polynomial-endofunctor)
open import foundation.structure-identity-principle using
  ( is-contr-total-Eq-structure)
open import foundation.universe-levels using (UU; Level; lsuc; _⊔_)

open import foundation-core.functoriality-dependent-pair-types using (equiv-tot)
```

## Idea

Given a polynomial endofunctor `P A B`, an algebra for `P A B` conisists of a type `X` and a map `P A B X → X`.

## Definitions

### Algebras for polynomial endofunctors

```agda
algebra-polynomial-endofunctor-UU :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  UU (lsuc l ⊔ l1 ⊔ l2)
algebra-polynomial-endofunctor-UU l A B =
  Σ (UU l) (λ X → type-polynomial-endofunctor A B X → X)
                                                  
type-algebra-polynomial-endofunctor :
  {l l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  algebra-polynomial-endofunctor-UU l A B → UU l
type-algebra-polynomial-endofunctor X = pr1 X
                                            
structure-algebra-polynomial-endofunctor :
  {l l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l A B) →
  type-polynomial-endofunctor A B (type-algebra-polynomial-endofunctor X) →
  type-algebra-polynomial-endofunctor X
structure-algebra-polynomial-endofunctor X = pr2 X
```

### Morphisms of algebras for polynomial endofunctors

```agda
-- Morphisms of algebras for polynomial endofunctors
  
hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (Y : algebra-polynomial-endofunctor-UU l4 A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
hom-algebra-polynomial-endofunctor {A = A} {B} X Y =
  Σ ( type-algebra-polynomial-endofunctor X →
      type-algebra-polynomial-endofunctor Y)
    ( λ f →
      ( f ∘ (structure-algebra-polynomial-endofunctor X)) ~
      ( ( structure-algebra-polynomial-endofunctor Y) ∘
        ( map-polynomial-endofunctor A B f)))

map-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (Y : algebra-polynomial-endofunctor-UU l4 A B) →
  hom-algebra-polynomial-endofunctor X Y →
  type-algebra-polynomial-endofunctor X →
  type-algebra-polynomial-endofunctor Y
map-hom-algebra-polynomial-endofunctor X Y f = pr1 f

structure-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (Y : algebra-polynomial-endofunctor-UU l4 A B) →
  (f : hom-algebra-polynomial-endofunctor X Y) →
  ( ( map-hom-algebra-polynomial-endofunctor X Y f) ∘
    ( structure-algebra-polynomial-endofunctor X)) ~
  ( ( structure-algebra-polynomial-endofunctor Y) ∘
    ( map-polynomial-endofunctor A B
      ( map-hom-algebra-polynomial-endofunctor X Y f)))
structure-hom-algebra-polynomial-endofunctor X Y f = pr2 f
```

## Properties

### The identity type of morphisms of algebras of polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y)
  where
  
  htpy-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-algebra-polynomial-endofunctor g =
    Σ ( map-hom-algebra-polynomial-endofunctor X Y f ~
        map-hom-algebra-polynomial-endofunctor X Y g)
      ( λ H →
        ( ( structure-hom-algebra-polynomial-endofunctor X Y f) ∙h
          ( ( structure-algebra-polynomial-endofunctor Y) ·l
            ( htpy-polynomial-endofunctor A B H))) ~
        ( ( H ·r structure-algebra-polynomial-endofunctor X) ∙h
          ( structure-hom-algebra-polynomial-endofunctor X Y g)))

  refl-htpy-hom-algebra-polynomial-endofunctor :
    htpy-hom-algebra-polynomial-endofunctor f
  pr1 refl-htpy-hom-algebra-polynomial-endofunctor = refl-htpy
  pr2 refl-htpy-hom-algebra-polynomial-endofunctor z =
    ( ap ( λ t →
           concat
             ( structure-hom-algebra-polynomial-endofunctor X Y f z)
             ( structure-algebra-polynomial-endofunctor Y
               ( map-polynomial-endofunctor A B
                 ( map-hom-algebra-polynomial-endofunctor X Y f) z))
             ( ap (structure-algebra-polynomial-endofunctor Y ) t))
         ( coh-refl-htpy-polynomial-endofunctor A B
           ( map-hom-algebra-polynomial-endofunctor X Y f) z)) ∙
    ( right-unit)

  htpy-eq-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    f ＝ g → htpy-hom-algebra-polynomial-endofunctor g
  htpy-eq-hom-algebra-polynomial-endofunctor .f refl =
    refl-htpy-hom-algebra-polynomial-endofunctor

  is-contr-total-htpy-hom-algebra-polynomial-endofunctor :
    is-contr
      ( Σ ( hom-algebra-polynomial-endofunctor X Y)
          ( htpy-hom-algebra-polynomial-endofunctor))
  is-contr-total-htpy-hom-algebra-polynomial-endofunctor =
    is-contr-total-Eq-structure
      ( λ ( g : pr1 X → pr1 Y)
          ( G : (g ∘ pr2 X) ~ ((pr2 Y) ∘ (map-polynomial-endofunctor A B g)))
          ( H : map-hom-algebra-polynomial-endofunctor X Y f ~ g) →
          ( ( structure-hom-algebra-polynomial-endofunctor X Y f) ∙h
            ( ( structure-algebra-polynomial-endofunctor Y) ·l
              ( htpy-polynomial-endofunctor A B H))) ~
          ( ( H ·r structure-algebra-polynomial-endofunctor X) ∙h G))
      ( is-contr-total-htpy (map-hom-algebra-polynomial-endofunctor X Y f))
      ( pair (map-hom-algebra-polynomial-endofunctor X Y f) refl-htpy)
      ( is-contr-equiv'
        ( Σ ( ( (pr1 f) ∘ pr2 X) ~
              ( pr2 Y ∘ map-polynomial-endofunctor A B (pr1 f)))
            ( λ H → (pr2 f) ~ H))
        ( equiv-tot
          ( λ H →
            ( equiv-concat-htpy
              ( λ x →
                ap ( concat
                     ( pr2 f x)
                     ( structure-algebra-polynomial-endofunctor Y
                       ( map-polynomial-endofunctor A B (pr1 f) x)))
                   ( ap ( ap (pr2 Y))
                        ( coh-refl-htpy-polynomial-endofunctor A B (pr1 f) x)))
              ( H)) ∘e
            ( equiv-concat-htpy right-unit-htpy H)))
        ( is-contr-total-htpy (pr2 f)))

  is-equiv-htpy-eq-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    is-equiv (htpy-eq-hom-algebra-polynomial-endofunctor g)
  is-equiv-htpy-eq-hom-algebra-polynomial-endofunctor =
    fundamental-theorem-id f
      ( refl-htpy-hom-algebra-polynomial-endofunctor)
      ( is-contr-total-htpy-hom-algebra-polynomial-endofunctor)
      ( htpy-eq-hom-algebra-polynomial-endofunctor)

  extensionality-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    (f ＝ g) ≃ htpy-hom-algebra-polynomial-endofunctor g
  pr1 (extensionality-hom-algebra-polynomial-endofunctor g) =
    htpy-eq-hom-algebra-polynomial-endofunctor g
  pr2 (extensionality-hom-algebra-polynomial-endofunctor g) =
    is-equiv-htpy-eq-hom-algebra-polynomial-endofunctor g
        
  eq-htpy-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    htpy-hom-algebra-polynomial-endofunctor g → f ＝ g
  eq-htpy-hom-algebra-polynomial-endofunctor g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-algebra-polynomial-endofunctor g)
```
