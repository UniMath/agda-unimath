# The universal property of set quotients

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-set-quotients where

open import foundation.contractible-maps using
  ( is-contr-map-is-equiv; is-equiv-is-contr-map)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; center; is-contr-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalence-relations using
  ( Eq-Rel; type-Eq-Rel)
open import foundation.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; is-equiv-has-inverse; is-equiv-comp;
    is-equiv-precomp-is-equiv; is-equiv-left-factor; map-equiv;
    is-subtype-is-equiv)
open import foundation.fibers-of-maps using (fib)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functions using (_∘_; id; precomp)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using
  ( _~_; refl-htpy; is-contr-total-htpy; inv-htpy; _·l_)
open import foundation.identity-types using (Id; ap; _∙_; inv; refl)
open import foundation.injective-maps using (is-injective-is-equiv)
open import foundation.propositions using
  ( is-prop; is-prop-Π'; is-prop-function-type; UU-Prop)
open import foundation.sets using
  ( UU-Set; type-Set; is-set; is-set-type-Set; type-hom-Set)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

The universal property of set quotients characterizes maps out of set quotients.

## Properties

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where
  
  reflects-Eq-Rel : {l3 : Level} {B : UU l3} → (A → B) → UU (l1 ⊔ (l2 ⊔ l3))
  reflects-Eq-Rel f = {x y : A} → type-Eq-Rel R x y → Id (f x) (f y)
  
  reflecting-map-Eq-Rel : {l3 : Level} → UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  reflecting-map-Eq-Rel B = Σ (A → B) reflects-Eq-Rel

  map-reflecting-map-Eq-Rel :
    {l3 : Level} {B : UU l3} → reflecting-map-Eq-Rel B → A → B
  map-reflecting-map-Eq-Rel = pr1

  reflects-map-reflecting-map-Eq-Rel :
    {l3 : Level} {B : UU l3} (f : reflecting-map-Eq-Rel B) →
    reflects-Eq-Rel (map-reflecting-map-Eq-Rel f)
  reflects-map-reflecting-map-Eq-Rel = pr2

  abstract
    is-prop-reflects-Eq-Rel :
      {l3 : Level} (B : UU-Set l3) (f : A → type-Set B) →
      is-prop (reflects-Eq-Rel f)
    is-prop-reflects-Eq-Rel B f =
      is-prop-Π'
        ( λ x →
          is-prop-Π'
            ( λ y →
              is-prop-function-type (is-set-type-Set B (f x) (f y))))

  reflects-Eq-Rel-Prop :
    {l3 : Level} (B : UU-Set l3) (f : A → type-Set B) → UU-Prop (l1 ⊔ l2 ⊔ l3)
  pr1 (reflects-Eq-Rel-Prop B f) = reflects-Eq-Rel f
  pr2 (reflects-Eq-Rel-Prop B f) = is-prop-reflects-Eq-Rel B f

-- We characterize the identity type of reflecting-map-Eq-Rel

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B))
  where

  htpy-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) → UU _
  htpy-reflecting-map-Eq-Rel g =
    pr1 f ~ pr1 g
  
  refl-htpy-reflecting-map-Eq-Rel :
    htpy-reflecting-map-Eq-Rel f
  refl-htpy-reflecting-map-Eq-Rel = refl-htpy
  
  htpy-eq-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    Id f g → htpy-reflecting-map-Eq-Rel g
  htpy-eq-reflecting-map-Eq-Rel .f refl =
    refl-htpy-reflecting-map-Eq-Rel

  abstract
    is-contr-total-htpy-reflecting-map-Eq-Rel :
      is-contr
        ( Σ (reflecting-map-Eq-Rel R (type-Set B)) htpy-reflecting-map-Eq-Rel)
    is-contr-total-htpy-reflecting-map-Eq-Rel =
      is-contr-total-Eq-subtype
        ( is-contr-total-htpy (pr1 f))
        ( is-prop-reflects-Eq-Rel R B)
        ( pr1 f)
        ( refl-htpy)
        ( pr2 f)

  abstract
    is-equiv-htpy-eq-reflecting-map-Eq-Rel :
      (g : reflecting-map-Eq-Rel R (type-Set B)) →
      is-equiv (htpy-eq-reflecting-map-Eq-Rel g)
    is-equiv-htpy-eq-reflecting-map-Eq-Rel =
      fundamental-theorem-id f
        refl-htpy-reflecting-map-Eq-Rel
        is-contr-total-htpy-reflecting-map-Eq-Rel
        htpy-eq-reflecting-map-Eq-Rel

  extensionality-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    Id f g ≃ htpy-reflecting-map-Eq-Rel g
  pr1 (extensionality-reflecting-map-Eq-Rel g) = htpy-eq-reflecting-map-Eq-Rel g
  pr2 (extensionality-reflecting-map-Eq-Rel g) =
    is-equiv-htpy-eq-reflecting-map-Eq-Rel g

  abstract
    eq-htpy-reflecting-map-Eq-Rel :
      (g : reflecting-map-Eq-Rel R (type-Set B)) →
      htpy-reflecting-map-Eq-Rel g → Id f g
    eq-htpy-reflecting-map-Eq-Rel g =
      map-inv-is-equiv (is-equiv-htpy-eq-reflecting-map-Eq-Rel g)

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B))
  where

  precomp-Set-Quotient :
    {l : Level} (X : UU-Set l) →
    (type-hom-Set B X) → reflecting-map-Eq-Rel R (type-Set X)
  pr1 (precomp-Set-Quotient X g) = g ∘ (map-reflecting-map-Eq-Rel R f)
  pr2 (precomp-Set-Quotient X g) r =
    ap g (reflects-map-reflecting-map-Eq-Rel R f r)

  precomp-id-Set-Quotient : Id (precomp-Set-Quotient B id) f
  precomp-id-Set-Quotient =
    eq-htpy-reflecting-map-Eq-Rel R B
      ( precomp-Set-Quotient B id)
      ( f)
      ( refl-htpy)

is-set-quotient :
  (l : Level) {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
is-set-quotient l R B f =
  (X : UU-Set l) → is-equiv (precomp-Set-Quotient R B f X)

module _
  (l : Level) {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B))
  where

  universal-property-set-quotient : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
  universal-property-set-quotient =
    (X : UU-Set l) (g : reflecting-map-Eq-Rel R (type-Set X)) →
    is-contr
      ( Σ ( type-hom-Set B X)
          ( λ h →
            ( h ∘ map-reflecting-map-Eq-Rel R f) ~
            ( map-reflecting-map-Eq-Rel R g)))

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : UU-Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B))
  where

  abstract
    universal-property-set-quotient-is-set-quotient :
      ({l : Level} → is-set-quotient l R B f) →
      ({l : Level} → universal-property-set-quotient l R B f)
    universal-property-set-quotient-is-set-quotient Q X g =
      is-contr-equiv'
        ( fib (precomp-Set-Quotient R B f X) g)
        ( equiv-tot
          ( λ h →
            extensionality-reflecting-map-Eq-Rel R X
              ( precomp-Set-Quotient R B f X h)
              ( g)))
        ( is-contr-map-is-equiv (Q X) g)

  map-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (Uf : {l : Level} → is-set-quotient l R B f)
    (C : UU-Set l4) (g : reflecting-map-Eq-Rel R (type-Set C)) →
    type-Set B → type-Set C
  map-universal-property-set-quotient-is-set-quotient Uf C g =
    pr1 (center (universal-property-set-quotient-is-set-quotient Uf C g))
  
  triangle-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (Uf : {l : Level} → is-set-quotient l R B f)
    (C : UU-Set l4) (g : reflecting-map-Eq-Rel R (type-Set C)) →
    ( ( map-universal-property-set-quotient-is-set-quotient Uf C g) ∘
      ( map-reflecting-map-Eq-Rel R f)) ~
    ( map-reflecting-map-Eq-Rel R g)
  triangle-universal-property-set-quotient-is-set-quotient Uf C g =
    ( pr2 (center (universal-property-set-quotient-is-set-quotient Uf C g)))

  is-set-quotient-universal-property-set-quotient :
    ({l : Level} → universal-property-set-quotient l R B f) →
    ({l : Level} → is-set-quotient l R B f)
  is-set-quotient-universal-property-set-quotient Uf X =
    is-equiv-is-contr-map
      ( λ g →
        is-contr-equiv
          ( Σ ( type-hom-Set B X)
              ( λ h →
                ( h ∘ map-reflecting-map-Eq-Rel R f) ~
                ( map-reflecting-map-Eq-Rel R g)))
          ( equiv-tot
            ( λ h →
              extensionality-reflecting-map-Eq-Rel R X
                ( precomp-Set-Quotient R B f X h)
                ( g)))
          ( Uf X g))


-- uniqueness of set quotients :

precomp-comp-Set-Quotient :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B))
  (C : UU-Set l4) (g : type-hom-Set B C)
  (D : UU-Set l5) (h : type-hom-Set C D) →
  Id ( precomp-Set-Quotient R B f D (h ∘ g))
     ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
precomp-comp-Set-Quotient R B f C g D h =
  eq-htpy-reflecting-map-Eq-Rel R D
    ( precomp-Set-Quotient R B f D (h ∘ g))
    ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
    ( refl-htpy)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B))
  (C : UU-Set l4) (g : reflecting-map-Eq-Rel R (type-Set C))
  {h : type-Set B → type-Set C}
  (H : (h ∘ map-reflecting-map-Eq-Rel R f) ~ map-reflecting-map-Eq-Rel R g)
  where

  abstract
    is-equiv-is-set-quotient-is-set-quotient :
      ({l : Level} → is-set-quotient l R B f) →
      ({l : Level} → is-set-quotient l R C g) →
      is-equiv h
    is-equiv-is-set-quotient-is-set-quotient Uf Ug =
      is-equiv-has-inverse 
        ( pr1 (center K))
        ( htpy-eq
          ( is-injective-is-equiv
            ( Ug C)
            { h ∘ k}
            { id}
            ( ( precomp-comp-Set-Quotient R C g B k C h) ∙
              ( ( ap (λ t → precomp-Set-Quotient R B t C h) α) ∙
                ( ( eq-htpy-reflecting-map-Eq-Rel R C
                    ( precomp-Set-Quotient R B f C h) g H) ∙
                  ( inv (precomp-id-Set-Quotient R C g)))))))
        ( htpy-eq
          ( is-injective-is-equiv
            ( Uf B)
            { k ∘ h}
            { id}
            ( ( precomp-comp-Set-Quotient R B f C h B k) ∙
              ( ( ap
                  ( λ t → precomp-Set-Quotient R C t B k)
                  ( eq-htpy-reflecting-map-Eq-Rel R C
                    ( precomp-Set-Quotient R B f C h) g H)) ∙
                ( ( α) ∙
                  ( inv (precomp-id-Set-Quotient R B f)))))))
      where
      K : is-contr
            ( Σ ( type-hom-Set C B)
                ( λ h →
                  ( h ∘ map-reflecting-map-Eq-Rel R g) ~
                  ( map-reflecting-map-Eq-Rel R f)))
      K = universal-property-set-quotient-is-set-quotient R C g Ug B f
      k : type-Set C → type-Set B
      k = pr1 (center K)
      α : Id (precomp-Set-Quotient R C g B k) f
      α = eq-htpy-reflecting-map-Eq-Rel R B
            ( precomp-Set-Quotient R C g B k)
            ( f)
            ( pr2 (center K))

  abstract
    is-set-quotient-is-set-quotient-is-equiv :
      is-equiv h → ({l : Level} → is-set-quotient l R B f) →
      {l : Level} → is-set-quotient l R C g
    is-set-quotient-is-set-quotient-is-equiv E Uf {l} X =
      is-equiv-comp
        ( precomp-Set-Quotient R C g X)
        ( precomp-Set-Quotient R B f X)
        ( precomp h (type-Set X))
        ( λ k →
          eq-htpy-reflecting-map-Eq-Rel R X
            ( precomp-Set-Quotient R C g X k)
            ( precomp-Set-Quotient R B f X (k ∘ h))
            ( inv-htpy (k ·l H)))
        ( is-equiv-precomp-is-equiv h E (type-Set X))
        ( Uf X)

  abstract
    is-set-quotient-is-equiv-is-set-quotient :
      ({l : Level} → is-set-quotient l R C g) → is-equiv h →
      {l : Level} → is-set-quotient l R B f
    is-set-quotient-is-equiv-is-set-quotient Ug E {l} X =
      is-equiv-left-factor
        ( precomp-Set-Quotient R C g X)
        ( precomp-Set-Quotient R B f X)
        ( precomp h (type-Set X))
        ( λ k →
          eq-htpy-reflecting-map-Eq-Rel R X
            ( precomp-Set-Quotient R C g X k)
            ( precomp-Set-Quotient R B f X (k ∘ h))
            ( inv-htpy (k ·l H)))
        ( Ug X)
        ( is-equiv-precomp-is-equiv h E (type-Set X))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B)) 
  (Uf : {l : Level} → is-set-quotient l R B f)
  (C : UU-Set l4) (g : reflecting-map-Eq-Rel R (type-Set C))
  (Ug : {l : Level} → is-set-quotient l R C g)
  where

  abstract
    uniqueness-set-quotient :
      is-contr
        ( Σ ( type-Set B ≃ type-Set C)
            ( λ e →
              ( map-equiv e ∘ map-reflecting-map-Eq-Rel R f) ~
              ( map-reflecting-map-Eq-Rel R g)))
    uniqueness-set-quotient =
      is-contr-total-Eq-subtype
        ( universal-property-set-quotient-is-set-quotient R B f Uf C g)
        ( is-subtype-is-equiv)
        ( map-universal-property-set-quotient-is-set-quotient R B f Uf C g)
        ( triangle-universal-property-set-quotient-is-set-quotient R B f Uf C g)
        ( is-equiv-is-set-quotient-is-set-quotient R B f C g
          ( triangle-universal-property-set-quotient-is-set-quotient
            R B f Uf C g)
          ( Uf)
          ( Ug))

  equiv-uniqueness-set-quotient : type-Set B ≃ type-Set C
  equiv-uniqueness-set-quotient =
    pr1 (center uniqueness-set-quotient)

  map-equiv-uniqueness-set-quotient : type-Set B → type-Set C
  map-equiv-uniqueness-set-quotient =  map-equiv equiv-uniqueness-set-quotient

  triangle-uniqueness-set-quotient :
    ( map-equiv-uniqueness-set-quotient ∘ map-reflecting-map-Eq-Rel R f) ~
    ( map-reflecting-map-Eq-Rel R g)
  triangle-uniqueness-set-quotient =
    pr2 (center uniqueness-set-quotient)
```
