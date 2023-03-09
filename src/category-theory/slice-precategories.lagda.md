# Slice precategories

```agda
module category-theory.slice-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories
open import category-theory.products-precategories
open import category-theory.pullbacks-precategories
open import category-theory.terminal-objects-precategories

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

The slice precategory of a precategory `C` over an object `X` of `C` is the category of objects of `C` equipped with a morphism into `X`.

## Definitions

### Objects and morphisms in the slice category

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2) (X : obj-Precat C)
  where

  obj-Slice-Precat : UU (l1 ⊔ l2)
  obj-Slice-Precat = Σ (obj-Precat C) (λ A → type-hom-Precat C A X)

  hom-Slice-Precat : obj-Slice-Precat → obj-Slice-Precat → Set l2
  hom-Slice-Precat (A , f) (B , g) =
    Σ-Set
      ( hom-Precat C A B)
      ( λ h → set-Prop (Id-Prop (hom-Precat C A X) f (comp-hom-Precat C g h)))

  type-hom-Slice-Precat : obj-Slice-Precat → obj-Slice-Precat → UU l2
  type-hom-Slice-Precat A B = type-Set (hom-Slice-Precat A B)

  is-set-type-hom-Slice-Precat :
    (A B : obj-Slice-Precat) → is-set (type-hom-Slice-Precat A B)
  is-set-type-hom-Slice-Precat A B = is-set-type-Set (hom-Slice-Precat A B)

  Eq-hom-Slice-Precat :
    {A B : obj-Slice-Precat} (f g : type-hom-Slice-Precat A B) → UU l2
  Eq-hom-Slice-Precat f g = (pr1 f ＝ pr1 g)

  refl-Eq-hom-Slice-Precat :
    {A B : obj-Slice-Precat} (f : type-hom-Slice-Precat A B) →
    Eq-hom-Slice-Precat f f
  refl-Eq-hom-Slice-Precat f = refl

  extensionality-hom-Slice-Precat :
    {A B : obj-Slice-Precat} (f g : type-hom-Slice-Precat A B) →
    (f ＝ g) ≃ Eq-hom-Slice-Precat f g
  extensionality-hom-Slice-Precat {A} {B} =
    extensionality-type-subtype'
      ( λ h →
        Id-Prop (hom-Precat C (pr1 A) X) (pr2 A) (comp-hom-Precat C (pr2 B) h))

  eq-hom-Slice-Precat :
    {A B : obj-Slice-Precat} (f g : type-hom-Slice-Precat A B) →
    Eq-hom-Slice-Precat f g → f ＝ g
  eq-hom-Slice-Precat f g =
    map-inv-equiv (extensionality-hom-Slice-Precat f g)
```

### Identity morphisms in the slice category

```agda
  id-hom-Slice-Precat :
    (A : obj-Slice-Precat) → type-hom-Slice-Precat A A
  pr1 (id-hom-Slice-Precat A) = id-hom-Precat C
  pr2 (id-hom-Slice-Precat A) = inv (right-unit-law-comp-hom-Precat C (pr2 A))
```

### Composition of morphisms in the slice category

```agda
  comp-hom-Slice-Precat :
    {A1 A2 A3 : obj-Slice-Precat} →
    type-hom-Slice-Precat A2 A3 → type-hom-Slice-Precat A1 A2 →
    type-hom-Slice-Precat A1 A3
  pr1 (comp-hom-Slice-Precat g f) = comp-hom-Precat C (pr1 g) (pr1 f)
  pr2 (comp-hom-Slice-Precat g f) =
    ( pr2 f) ∙
    ( ( ap (λ u → comp-hom-Precat C u (pr1 f)) (pr2 g)) ∙
      ( assoc-comp-hom-Precat C _ (pr1 g) (pr1 f)))
```

### Associativity of composition of morphisms in the slice category

```agda
  assoc-comp-hom-Slice-Precat :
    {A1 A2 A3 A4 : obj-Slice-Precat} →
    (h : type-hom-Slice-Precat A3 A4) (g : type-hom-Slice-Precat A2 A3)
    (f : type-hom-Slice-Precat A1 A2) →
    ( comp-hom-Slice-Precat (comp-hom-Slice-Precat h g) f) ＝
    ( comp-hom-Slice-Precat h (comp-hom-Slice-Precat g f))
  assoc-comp-hom-Slice-Precat h g f =
    eq-hom-Slice-Precat
      ( comp-hom-Slice-Precat (comp-hom-Slice-Precat h g) f)
      ( comp-hom-Slice-Precat h (comp-hom-Slice-Precat g f))
      ( assoc-comp-hom-Precat C (pr1 h) (pr1 g) (pr1 f))
```

### The left unit law for composition of morphisms in the slice category

```agda
  left-unit-law-comp-hom-Slice-Precat :
    {A B : obj-Slice-Precat} (f : type-hom-Slice-Precat A B) →
    comp-hom-Slice-Precat (id-hom-Slice-Precat B) f ＝ f
  left-unit-law-comp-hom-Slice-Precat f =
    eq-hom-Slice-Precat
      ( comp-hom-Slice-Precat (id-hom-Slice-Precat _) f)
      ( f)
      ( left-unit-law-comp-hom-Precat C (pr1 f))
```

### The right unit law for composition of morphisms in the slice category

```agda
  right-unit-law-comp-hom-Slice-Precat :
    {A B : obj-Slice-Precat} (f : type-hom-Slice-Precat A B) →
    comp-hom-Slice-Precat f (id-hom-Slice-Precat A) ＝ f
  right-unit-law-comp-hom-Slice-Precat f =
    eq-hom-Slice-Precat
      ( comp-hom-Slice-Precat f (id-hom-Slice-Precat _))
      ( f)
      ( right-unit-law-comp-hom-Precat C (pr1 f))
```

### The slice precategory

```agda
  Slice-Precat : Precat (l1 ⊔ l2) l2
  pr1 Slice-Precat = obj-Slice-Precat
  pr1 (pr2 Slice-Precat) = hom-Slice-Precat
  pr1 (pr1 (pr2 (pr2 Slice-Precat))) = comp-hom-Slice-Precat
  pr2 (pr1 (pr2 (pr2 Slice-Precat))) = assoc-comp-hom-Slice-Precat
  pr1 (pr2 (pr2 (pr2 Slice-Precat))) = id-hom-Slice-Precat
  pr1 (pr2 (pr2 (pr2 (pr2 Slice-Precat)))) = left-unit-law-comp-hom-Slice-Precat
  pr2 (pr2 (pr2 (pr2 (pr2 Slice-Precat)))) = right-unit-law-comp-hom-Slice-Precat
```

## Properties

### The slice precategory always has a terminal object

The terminal object in the slice (pre-)category `C/X` is the identity morphism `id : hom X X`.

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2) (X : obj-Precat C)
  where

  terminal-object-Slice-Precat : terminal-object (Slice-Precat C X)
  pr1 terminal-object-Slice-Precat = (X , id-hom-Precat C)
  pr2 terminal-object-Slice-Precat (A , f) =
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

    map-is-pullback-is-product-Slice-Precat :
      is-pullback C A X Y f g W p₁ p₂ α →
      is-product (Slice-Precat C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂)
    map-is-pullback-is-product-Slice-Precat ϕ (Z , .(comp-hom-Precat C f h₁)) (h₁ , refl) (h₂ , β₂) =
      is-contr-Σ-is-prop c d q σ
      where
        c : type-hom-Precat (Slice-Precat C A) (Z , comp-hom-Precat C f h₁) (W , p)
        pr1 c = pr1 (pr1 (ϕ Z h₁ h₂ β₂))
        pr2 c =
          ap (comp-hom-Precat C f) (inv (pr1 (pr2 (pr1 (ϕ Z h₁ h₂ β₂))))) ∙
          (inv (assoc-comp-hom-Precat C f p₁ _) ∙
          ap (λ k → comp-hom-Precat C k (pr1 (pr1 (ϕ Z h₁ h₂ β₂)))) (inv α₁))

        d : (comp-hom-Precat (Slice-Precat C A) (p₁ , α₁) c ＝ (h₁ , refl)) ×
            (comp-hom-Precat (Slice-Precat C A) (p₂ , α₂) c ＝ (h₂ , β₂))
        pr1 d = eq-hom-Slice-Precat C A _ _ (pr1 (pr2 (pr1 (ϕ Z h₁ h₂ β₂))))
        pr2 d = eq-hom-Slice-Precat C A _ _ (pr2 (pr2 (pr1 (ϕ Z h₁ h₂ β₂))))

        q : ∀ k →
          is-prop
            ( (comp-hom-Precat (Slice-Precat C A) (p₁ , α₁) k ＝ (h₁ , refl)) ×
            ( (comp-hom-Precat (Slice-Precat C A) (p₂ , α₂) k ＝ (h₂ , β₂))))
        q k =
          is-prop-prod
            ( is-set-type-Set (hom-Slice-Precat C A _ _) _ _)
            ( is-set-type-Set (hom-Slice-Precat C A _ _) _ _)

        σ : ∀ k →
          ( comp-hom-Precat (Slice-Precat C A) (p₁ , α₁) k ＝ (h₁ , refl)) ×
          ( comp-hom-Precat (Slice-Precat C A) (p₂ , α₂) k ＝ (h₂ , β₂)) →
          c ＝ k
        σ (k , γ) (γ₁ , γ₂) =
          eq-hom-Slice-Precat C A _ _
            ( ap pr1 (pr2 (ϕ Z h₁ h₂ β₂) (k , (ap pr1 γ₁ , ap pr1 γ₂))))

    map-inv-is-pullback-is-product-Slice-Precat :
      is-product (Slice-Precat C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂) →
      is-pullback C A X Y f g W p₁ p₂ α
    map-inv-is-pullback-is-product-Slice-Precat ψ W' p₁' p₂' α' =
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
                   ( eq-hom-Slice-Precat C A _ _ γ₁) ,
                   ( eq-hom-Slice-Precat C A _ _ γ₂)))

    equiv-is-pullback-is-product-Slice-Precat :
      is-pullback C A X Y f g W p₁ p₂ α ≃
      is-product (Slice-Precat C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂)
    equiv-is-pullback-is-product-Slice-Precat =
      equiv-prop
        ( is-prop-is-pullback C A X Y f g W p₁ p₂ α)
        ( is-prop-is-product (Slice-Precat C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂))
        ( map-is-pullback-is-product-Slice-Precat)
        ( map-inv-is-pullback-is-product-Slice-Precat)

  map-pullback-product-Slice-Precat :
    pullback C A X Y f g →
    product (Slice-Precat C A) (X , f) (Y , g)
  pr1 (map-pullback-product-Slice-Precat (W , p₁ , p₂ , α , q)) = (W , comp-hom-Precat C f p₁)
  pr1 (pr2 (map-pullback-product-Slice-Precat (W , p₁ , p₂ , α , q))) = (p₁ , refl)
  pr1 (pr2 (pr2 (map-pullback-product-Slice-Precat (W , p₁ , p₂ , α , q)))) = (p₂ , α)
  pr2 (pr2 (pr2 (map-pullback-product-Slice-Precat (W , p₁ , p₂ , α , q)))) =
    map-is-pullback-is-product-Slice-Precat p₁ p₂ (comp-hom-Precat C f p₁) refl α α q

  map-inv-pullback-product-Slice-Precat :
    product (Slice-Precat C A) (X , f) (Y , g) →
    pullback C A X Y f g
  pr1 (map-inv-pullback-product-Slice-Precat ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q)) = Z
  pr1 (pr2 (map-inv-pullback-product-Slice-Precat ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q))) = h₁
  pr1 (pr2 (pr2 (map-inv-pullback-product-Slice-Precat ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q)))) = h₂
  pr1 (pr2 (pr2 (pr2 (map-inv-pullback-product-Slice-Precat ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q))))) = inv β₁ ∙ β₂
  pr2 (pr2 (pr2 (pr2 (map-inv-pullback-product-Slice-Precat ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q))))) =
    map-inv-is-pullback-is-product-Slice-Precat h₁ h₂ h β₁ β₂ (inv β₁ ∙ β₂) q

  issec-map-inv-pullback-product-Slice-Precat :
    (map-pullback-product-Slice-Precat ∘ map-inv-pullback-product-Slice-Precat) ~ id
  issec-map-inv-pullback-product-Slice-Precat ((Z , .(comp-hom-Precat C f h₁)) , (h₁ , refl) , (h₂ , β₂) , q) =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
         ( refl)
         ( eq-type-subtype
             (λ _ → is-product-Prop (Slice-Precat C A) (X , f) (Y , g) _ _ _)
             ( refl)))

  isretr-map-inv-pullback-product-Slice-Precat :
    (map-inv-pullback-product-Slice-Precat ∘ map-pullback-product-Slice-Precat) ~ id
  isretr-map-inv-pullback-product-Slice-Precat (W , p₁ , p₂ , α , q) =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
          ( refl)
          ( eq-pair-Σ
              ( refl)
              ( eq-type-subtype
                  (λ _ → is-pullback-Prop C A X Y f g _ _ _ α)
                  ( refl))))

  equiv-pullback-product-Slice-Precat : pullback C A X Y f g ≃ product (Slice-Precat C A) (X , f) (Y , g)
  pr1 equiv-pullback-product-Slice-Precat = map-pullback-product-Slice-Precat
  pr2 equiv-pullback-product-Slice-Precat =
    is-equiv-has-inverse
      map-inv-pullback-product-Slice-Precat
      issec-map-inv-pullback-product-Slice-Precat
      isretr-map-inv-pullback-product-Slice-Precat
```
