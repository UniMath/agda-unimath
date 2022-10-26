---
title: Slice precategories
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.slice-precategories where

open import category-theory.precategories
open import category-theory.products-precategories
open import category-theory.pullbacks-precategories
open import category-theory.terminal-objects-precategories

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using
  ( is-contr-equiv; is-contr-total-path; is-contr-Σ-is-prop)
open import foundation.dependent-pair-types using (Σ; _,_; pr1; pr2)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equational-reasoning
open import foundation.equivalences using
  ( _≃_; map-inv-equiv; _∘e_; is-equiv-has-inverse)
open import foundation.functions
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot; equiv-Σ)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using
  ( _＝_; refl; inv; _∙_; ap; equiv-concat')
open import foundation.propositions using
  ( prod-Prop; equiv-prop; is-prop; is-prop-prod)
open import foundation.sets using
  ( Set; Σ-Set; set-Prop; Id-Prop; type-Set; is-set; is-set-type-Set)
open import foundation.subtypes using
  ( extensionality-type-subtype; eq-subtype)
open import foundation.type-arithmetic-dependent-pair-types using
  ( inv-left-unit-law-Σ-is-contr; assoc-Σ)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The slice precategory of a precategory `C` over an object `X` of `C` is the category of objects of `C` equipped with a morphism into `X`.

## Definitions

### Objects and morphisms in the slice category

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2) (X : obj-Precat C)
  where

  obj-slice-Precat : UU (l1 ⊔ l2)
  obj-slice-Precat = Σ (obj-Precat C) (λ A → type-hom-Precat C A X)

  hom-slice-Precat : obj-slice-Precat → obj-slice-Precat → Set l2
  hom-slice-Precat (pair A f) (pair B g) =
    Σ-Set
      ( hom-Precat C A B)
      ( λ h → set-Prop (Id-Prop (hom-Precat C A X) f (comp-hom-Precat C g h)))

  type-hom-slice-Precat : obj-slice-Precat → obj-slice-Precat → UU l2
  type-hom-slice-Precat A B = type-Set (hom-slice-Precat A B)

  is-set-type-hom-slice-Precat :
    (A B : obj-slice-Precat) → is-set (type-hom-slice-Precat A B)
  is-set-type-hom-slice-Precat A B = is-set-type-Set (hom-slice-Precat A B)

  Eq-hom-slice-Precat :
    {A B : obj-slice-Precat} (f g : type-hom-slice-Precat A B) → UU l2
  Eq-hom-slice-Precat f g = (pr1 f ＝ pr1 g)

  refl-Eq-hom-slice-Precat :
    {A B : obj-slice-Precat} (f : type-hom-slice-Precat A B) →
    Eq-hom-slice-Precat f f
  refl-Eq-hom-slice-Precat f = refl

  extensionality-hom-slice-Precat :
    {A B : obj-slice-Precat} (f g : type-hom-slice-Precat A B) →
    (f ＝ g) ≃ Eq-hom-slice-Precat f g
  extensionality-hom-slice-Precat {A} {B} =
    extensionality-type-subtype'
      ( λ h →
        Id-Prop (hom-Precat C (pr1 A) X) (pr2 A) (comp-hom-Precat C (pr2 B) h))

  eq-hom-slice-Precat :
    {A B : obj-slice-Precat} (f g : type-hom-slice-Precat A B) →
    Eq-hom-slice-Precat f g → f ＝ g
  eq-hom-slice-Precat f g =
    map-inv-equiv (extensionality-hom-slice-Precat f g)
```

### Identity morphisms in the slice category

```agda
  id-hom-slice-Precat :
    (A : obj-slice-Precat) → type-hom-slice-Precat A A
  pr1 (id-hom-slice-Precat A) = id-hom-Precat C
  pr2 (id-hom-slice-Precat A) = inv (right-unit-law-comp-hom-Precat C (pr2 A))
```

### Composition of morphisms in the slice category

```agda
  comp-hom-slice-Precat :
    {A1 A2 A3 : obj-slice-Precat} →
    type-hom-slice-Precat A2 A3 → type-hom-slice-Precat A1 A2 →
    type-hom-slice-Precat A1 A3
  pr1 (comp-hom-slice-Precat g f) = comp-hom-Precat C (pr1 g) (pr1 f)
  pr2 (comp-hom-slice-Precat g f) =
    ( pr2 f) ∙
    ( ( ap (λ u → comp-hom-Precat C u (pr1 f)) (pr2 g)) ∙
      ( assoc-comp-hom-Precat C _ (pr1 g) (pr1 f)))
```

### Associativity of composition of morphisms in the slice category

```agda
  assoc-comp-hom-slice-Precat :
    {A1 A2 A3 A4 : obj-slice-Precat} →
    (h : type-hom-slice-Precat A3 A4) (g : type-hom-slice-Precat A2 A3)
    (f : type-hom-slice-Precat A1 A2) →
    ( comp-hom-slice-Precat (comp-hom-slice-Precat h g) f) ＝
    ( comp-hom-slice-Precat h (comp-hom-slice-Precat g f))
  assoc-comp-hom-slice-Precat h g f =
    eq-hom-slice-Precat
      ( comp-hom-slice-Precat (comp-hom-slice-Precat h g) f)
      ( comp-hom-slice-Precat h (comp-hom-slice-Precat g f))
      ( assoc-comp-hom-Precat C (pr1 h) (pr1 g) (pr1 f))
```

### The left unit law for composition of morphisms in the slice category

```agda
  left-unit-law-comp-hom-slice-Precat :
    {A B : obj-slice-Precat} (f : type-hom-slice-Precat A B) →
    comp-hom-slice-Precat (id-hom-slice-Precat B) f ＝ f
  left-unit-law-comp-hom-slice-Precat f =
    eq-hom-slice-Precat
      ( comp-hom-slice-Precat (id-hom-slice-Precat _) f)
      ( f)
      ( left-unit-law-comp-hom-Precat C (pr1 f))
```

### The right unit law for composition of morphisms in the slice category

```agda
  right-unit-law-comp-hom-slice-Precat :
    {A B : obj-slice-Precat} (f : type-hom-slice-Precat A B) →
    comp-hom-slice-Precat f (id-hom-slice-Precat A) ＝ f
  right-unit-law-comp-hom-slice-Precat f =
    eq-hom-slice-Precat
      ( comp-hom-slice-Precat f (id-hom-slice-Precat _))
      ( f)
      ( right-unit-law-comp-hom-Precat C (pr1 f))
```

### The slice precategory

```agda
  slice-Precat : Precat (l1 ⊔ l2) l2
  pr1 slice-Precat = obj-slice-Precat
  pr1 (pr2 slice-Precat) = hom-slice-Precat
  pr1 (pr1 (pr2 (pr2 slice-Precat))) = comp-hom-slice-Precat
  pr2 (pr1 (pr2 (pr2 slice-Precat))) = assoc-comp-hom-slice-Precat
  pr1 (pr2 (pr2 (pr2 slice-Precat))) = id-hom-slice-Precat
  pr1 (pr2 (pr2 (pr2 (pr2 slice-Precat)))) = left-unit-law-comp-hom-slice-Precat
  pr2 (pr2 (pr2 (pr2 (pr2 slice-Precat)))) = right-unit-law-comp-hom-slice-Precat
```

## Properties

### The slice precategory always has a terminal object

The terminal object in the slice (pre-)category `C/X` is the identity morphism `id : hom X X`.

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2) (X : obj-Precat C)
  where

  terminal-object-slice-Precat : terminal-object (slice-Precat C X)
  pr1 terminal-object-slice-Precat = (X , id-hom-Precat C)
  pr2 terminal-object-slice-Precat (A , f) =
    is-contr-equiv
      ( Σ (type-hom-Precat C A X) (λ g → f ＝ g))
      ( equiv-tot (λ g → equiv-concat' f (left-unit-law-comp-hom-Precat C g)))
      ( is-contr-total-path f)
```

### Products in slice precategories are pullbacks in the original category

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2) {A X Y : obj-Precat C}
  (f : type-hom-Precat C X A) (g : type-hom-Precat C Y A)
  where

  module _ {W : obj-Precat C}
    (p₁ : type-hom-Precat C W X) (p₂ : type-hom-Precat C W Y)
    (p : type-hom-Precat C W A)
    (α₁ : p ＝ comp-hom-Precat C f p₁) (α₂ : p ＝ comp-hom-Precat C g p₂)
    (α : comp-hom-Precat C f p₁ ＝ comp-hom-Precat C g p₂)
    where

    map-is-pullback-is-product-slice-Precat :
      is-pullback C A X Y f g W p₁ p₂ α →
      is-product (slice-Precat C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂)
    map-is-pullback-is-product-slice-Precat ϕ (Z , .(comp-hom-Precat C f h₁)) (h₁ , refl) (h₂ , β₂) =
      is-contr-Σ-is-prop c d q σ
      where
        c : type-hom-Precat (slice-Precat C A) (Z , comp-hom-Precat C f h₁) (W , p)
        pr1 c = pr1 (pr1 (ϕ Z h₁ h₂ β₂))
        pr2 c =
          ap (comp-hom-Precat C f) (inv (pr1 (pr2 (pr1 (ϕ Z h₁ h₂ β₂))))) ∙
          (inv (assoc-comp-hom-Precat C f p₁ _) ∙
          ap (λ k → comp-hom-Precat C k (pr1 (pr1 (ϕ Z h₁ h₂ β₂)))) (inv α₁))

        d : (comp-hom-Precat (slice-Precat C A) (p₁ , α₁) c ＝ (h₁ , refl)) ×
            (comp-hom-Precat (slice-Precat C A) (p₂ , α₂) c ＝ (h₂ , β₂))
        pr1 d = eq-hom-slice-Precat C A _ _ (pr1 (pr2 (pr1 (ϕ Z h₁ h₂ β₂))))
        pr2 d = eq-hom-slice-Precat C A _ _ (pr2 (pr2 (pr1 (ϕ Z h₁ h₂ β₂))))

        q : ∀ k →
          is-prop
            ( (comp-hom-Precat (slice-Precat C A) (p₁ , α₁) k ＝ (h₁ , refl)) ×
            ( (comp-hom-Precat (slice-Precat C A) (p₂ , α₂) k ＝ (h₂ , β₂))))
        q k =
          is-prop-prod
            ( is-set-type-Set (hom-slice-Precat C A _ _) _ _)
            ( is-set-type-Set (hom-slice-Precat C A _ _) _ _)

        σ : ∀ k →
          ( comp-hom-Precat (slice-Precat C A) (p₁ , α₁) k ＝ (h₁ , refl)) ×
          ( comp-hom-Precat (slice-Precat C A) (p₂ , α₂) k ＝ (h₂ , β₂)) →
          c ＝ k
        σ (k , γ) (γ₁ , γ₂) =
          eq-hom-slice-Precat C A _ _
            ( ap pr1 (pr2 (ϕ Z h₁ h₂ β₂) (k , (ap pr1 γ₁ , ap pr1 γ₂))))

    map-inv-is-pullback-is-product-slice-Precat :
      is-product (slice-Precat C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂) →
      is-pullback C A X Y f g W p₁ p₂ α
    map-inv-is-pullback-is-product-slice-Precat ψ W' p₁' p₂' α' =
      is-contr-Σ-is-prop k γ q σ
      where
        k : type-hom-Precat C W' W
        k = pr1 (pr1 (pr1 (ψ (W' , comp-hom-Precat C f p₁') (p₁' , refl) (p₂' , α'))))

        γ : (comp-hom-Precat C p₁ k ＝ p₁') × (comp-hom-Precat C p₂ k ＝ p₂')
        pr1 γ = ap pr1 (pr1 (pr2 (pr1 (ψ (W' , comp-hom-Precat C f p₁') (p₁' , refl) (p₂' , α')))))
        pr2 γ = ap pr1 (pr2 (pr2 (pr1 (ψ (W' , comp-hom-Precat C f p₁') (p₁' , refl) (p₂' , α')))))

        q : ∀ k' →
          is-prop
            (( comp-hom-Precat C p₁ k' ＝ p₁') ×
            ( comp-hom-Precat C p₂ k' ＝ p₂'))
        q k' =
          is-prop-prod
            ( is-set-type-Set (hom-Precat C _ _) _ _)
            ( is-set-type-Set (hom-Precat C _ _) _ _)

        σ : (k' : type-hom-Precat C W' W) →
            (γ' : (comp-hom-Precat C p₁ k' ＝ p₁') × (comp-hom-Precat C p₂ k' ＝ p₂')) →
            k ＝ k'
        σ k' (γ₁ , γ₂) =
          ap (pr1 ∘ pr1)
             (pr2 (ψ (W' , comp-hom-Precat C f p₁') (p₁' , refl) (p₂' , α'))
                  (( k' ,
                   ( ap (comp-hom-Precat C f) (inv γ₁) ∙
                       (inv (assoc-comp-hom-Precat C f p₁ k') ∙
                       ap (λ l → comp-hom-Precat C l k') (inv α₁)))) ,
                   ( eq-hom-slice-Precat C A _ _ γ₁) ,
                   ( eq-hom-slice-Precat C A _ _ γ₂)))

    equiv-is-pullback-is-product-slice-Precat :
      is-pullback C A X Y f g W p₁ p₂ α ≃
      is-product (slice-Precat C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂)
    equiv-is-pullback-is-product-slice-Precat =
      equiv-prop
        ( is-prop-is-pullback C A X Y f g W p₁ p₂ α)
        ( is-prop-is-product (slice-Precat C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂))
        ( map-is-pullback-is-product-slice-Precat)
        ( map-inv-is-pullback-is-product-slice-Precat)

  map-pullback-product-slice-Precat :
    pullback C A X Y f g →
    product (slice-Precat C A) (X , f) (Y , g)
  pr1 (map-pullback-product-slice-Precat (W , p₁ , p₂ , α , q)) = (W , comp-hom-Precat C f p₁)
  pr1 (pr2 (map-pullback-product-slice-Precat (W , p₁ , p₂ , α , q))) = (p₁ , refl)
  pr1 (pr2 (pr2 (map-pullback-product-slice-Precat (W , p₁ , p₂ , α , q)))) = (p₂ , α)
  pr2 (pr2 (pr2 (map-pullback-product-slice-Precat (W , p₁ , p₂ , α , q)))) =
    map-is-pullback-is-product-slice-Precat p₁ p₂ (comp-hom-Precat C f p₁) refl α α q

  map-inv-pullback-product-slice-Precat :
    product (slice-Precat C A) (X , f) (Y , g) →
    pullback C A X Y f g
  pr1 (map-inv-pullback-product-slice-Precat ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q)) = Z
  pr1 (pr2 (map-inv-pullback-product-slice-Precat ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q))) = h₁
  pr1 (pr2 (pr2 (map-inv-pullback-product-slice-Precat ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q)))) = h₂
  pr1 (pr2 (pr2 (pr2 (map-inv-pullback-product-slice-Precat ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q))))) = inv β₁ ∙ β₂
  pr2 (pr2 (pr2 (pr2 (map-inv-pullback-product-slice-Precat ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q))))) =
    map-inv-is-pullback-is-product-slice-Precat h₁ h₂ h β₁ β₂ (inv β₁ ∙ β₂) q

  issec-map-inv-pullback-product-slice-Precat :
    (map-pullback-product-slice-Precat ∘ map-inv-pullback-product-slice-Precat) ~ id
  issec-map-inv-pullback-product-slice-Precat ((Z , .(comp-hom-Precat C f h₁)) , (h₁ , refl) , (h₂ , β₂) , q) =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
         ( refl)
         ( eq-subtype
             (λ _ → is-product-Prop (slice-Precat C A) (X , f) (Y , g) _ _ _)
             ( refl)))

  isretr-map-inv-pullback-product-slice-Precat :
    (map-inv-pullback-product-slice-Precat ∘ map-pullback-product-slice-Precat) ~ id
  isretr-map-inv-pullback-product-slice-Precat (W , p₁ , p₂ , α , q) =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
          ( refl)
          ( eq-pair-Σ
              ( refl)
              ( eq-subtype
                  (λ _ → is-pullback-Prop C A X Y f g _ _ _ α)
                  ( refl))))

  equiv-pullback-product-slice-Precat : pullback C A X Y f g ≃ product (slice-Precat C A) (X , f) (Y , g)
  pr1 equiv-pullback-product-slice-Precat = map-pullback-product-slice-Precat
  pr2 equiv-pullback-product-slice-Precat =
    is-equiv-has-inverse
      map-inv-pullback-product-slice-Precat
      issec-map-inv-pullback-product-slice-Precat
      isretr-map-inv-pullback-product-slice-Precat
```
