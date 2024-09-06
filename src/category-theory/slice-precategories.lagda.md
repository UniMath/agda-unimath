# Slice precategories

```agda
module category-theory.slice-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.precategories
open import category-theory.products-in-precategories
open import category-theory.pullbacks-in-precategories
open import category-theory.terminal-objects-precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

The slice precategory of a precategory `C` over an object `X` of `C` is the
category of objects of `C` equipped with a morphism into `X`.

## Definitions

### Objects and morphisms in the slice category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  obj-Slice-Precategory : UU (l1 ⊔ l2)
  obj-Slice-Precategory =
    Σ (obj-Precategory C) (λ A → hom-Precategory C A X)

  hom-set-Slice-Precategory :
    obj-Slice-Precategory → obj-Slice-Precategory → Set l2
  hom-set-Slice-Precategory (A , f) (B , g) =
    Σ-Set
      ( hom-set-Precategory C A B)
      ( λ h →
        set-Prop
          ( Id-Prop (hom-set-Precategory C A X) f (comp-hom-Precategory C g h)))

  hom-Slice-Precategory :
    obj-Slice-Precategory → obj-Slice-Precategory → UU l2
  hom-Slice-Precategory A B = type-Set (hom-set-Slice-Precategory A B)

  is-set-hom-Slice-Precategory :
    (A B : obj-Slice-Precategory) → is-set (hom-Slice-Precategory A B)
  is-set-hom-Slice-Precategory A B =
    is-set-type-Set (hom-set-Slice-Precategory A B)

  Eq-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory}
    (f g : hom-Slice-Precategory A B) → UU l2
  Eq-hom-Slice-Precategory f g = (pr1 f ＝ pr1 g)

  refl-Eq-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory} (f : hom-Slice-Precategory A B) →
    Eq-hom-Slice-Precategory f f
  refl-Eq-hom-Slice-Precategory f = refl

  extensionality-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory} (f g : hom-Slice-Precategory A B) →
    (f ＝ g) ≃ Eq-hom-Slice-Precategory f g
  extensionality-hom-Slice-Precategory {A} {B} =
    extensionality-type-subtype'
      ( λ h →
        Id-Prop
          ( hom-set-Precategory C (pr1 A) X)
          ( pr2 A)
          ( comp-hom-Precategory C (pr2 B) h))

  eq-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory} (f g : hom-Slice-Precategory A B) →
    Eq-hom-Slice-Precategory f g → f ＝ g
  eq-hom-Slice-Precategory f g =
    map-inv-equiv (extensionality-hom-Slice-Precategory f g)
```

### Identity morphisms in the slice category

```agda
  id-hom-Slice-Precategory :
    (A : obj-Slice-Precategory) → hom-Slice-Precategory A A
  pr1 (id-hom-Slice-Precategory A) = id-hom-Precategory C
  pr2 (id-hom-Slice-Precategory A) =
    inv (right-unit-law-comp-hom-Precategory C (pr2 A))
```

### Composition of morphisms in the slice category

```agda
  comp-hom-Slice-Precategory :
    {A1 A2 A3 : obj-Slice-Precategory} →
    hom-Slice-Precategory A2 A3 → hom-Slice-Precategory A1 A2 →
    hom-Slice-Precategory A1 A3
  pr1 (comp-hom-Slice-Precategory g f) = comp-hom-Precategory C (pr1 g) (pr1 f)
  pr2 (comp-hom-Slice-Precategory g f) =
    ( pr2 f) ∙
    ( ( ap (λ u → comp-hom-Precategory C u (pr1 f)) (pr2 g)) ∙
      ( associative-comp-hom-Precategory C _ (pr1 g) (pr1 f)))
```

### Associativity of composition of morphisms in the slice category

```agda
  associative-comp-hom-Slice-Precategory :
    {A1 A2 A3 A4 : obj-Slice-Precategory} →
    (h : hom-Slice-Precategory A3 A4)
    (g : hom-Slice-Precategory A2 A3)
    (f : hom-Slice-Precategory A1 A2) →
    comp-hom-Slice-Precategory (comp-hom-Slice-Precategory h g) f ＝
    comp-hom-Slice-Precategory h (comp-hom-Slice-Precategory g f)
  associative-comp-hom-Slice-Precategory h g f =
    eq-hom-Slice-Precategory
      ( comp-hom-Slice-Precategory (comp-hom-Slice-Precategory h g) f)
      ( comp-hom-Slice-Precategory h (comp-hom-Slice-Precategory g f))
      ( associative-comp-hom-Precategory C (pr1 h) (pr1 g) (pr1 f))

  involutive-eq-associative-comp-hom-Slice-Precategory :
    {A1 A2 A3 A4 : obj-Slice-Precategory} →
    (h : hom-Slice-Precategory A3 A4)
    (g : hom-Slice-Precategory A2 A3)
    (f : hom-Slice-Precategory A1 A2) →
    comp-hom-Slice-Precategory (comp-hom-Slice-Precategory h g) f ＝ⁱ
    comp-hom-Slice-Precategory h (comp-hom-Slice-Precategory g f)
  involutive-eq-associative-comp-hom-Slice-Precategory h g f =
    involutive-eq-eq (associative-comp-hom-Slice-Precategory h g f)
```

### The left unit law for composition of morphisms in the slice category

```agda
  left-unit-law-comp-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory} (f : hom-Slice-Precategory A B) →
    comp-hom-Slice-Precategory (id-hom-Slice-Precategory B) f ＝ f
  left-unit-law-comp-hom-Slice-Precategory f =
    eq-hom-Slice-Precategory
      ( comp-hom-Slice-Precategory (id-hom-Slice-Precategory _) f)
      ( f)
      ( left-unit-law-comp-hom-Precategory C (pr1 f))
```

### The right unit law for composition of morphisms in the slice category

```agda
  right-unit-law-comp-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory} (f : hom-Slice-Precategory A B) →
    comp-hom-Slice-Precategory f (id-hom-Slice-Precategory A) ＝ f
  right-unit-law-comp-hom-Slice-Precategory f =
    eq-hom-Slice-Precategory
      ( comp-hom-Slice-Precategory f (id-hom-Slice-Precategory _))
      ( f)
      ( right-unit-law-comp-hom-Precategory C (pr1 f))
```

### The slice precategory

```agda
  Slice-Precategory : Precategory (l1 ⊔ l2) l2
  pr1 Slice-Precategory = obj-Slice-Precategory
  pr1 (pr2 Slice-Precategory) = hom-set-Slice-Precategory
  pr1 (pr1 (pr2 (pr2 Slice-Precategory))) = comp-hom-Slice-Precategory
  pr2 (pr1 (pr2 (pr2 Slice-Precategory))) =
    involutive-eq-associative-comp-hom-Slice-Precategory
  pr1 (pr2 (pr2 (pr2 Slice-Precategory))) = id-hom-Slice-Precategory
  pr1 (pr2 (pr2 (pr2 (pr2 Slice-Precategory)))) =
    left-unit-law-comp-hom-Slice-Precategory
  pr2 (pr2 (pr2 (pr2 (pr2 Slice-Precategory)))) =
    right-unit-law-comp-hom-Slice-Precategory
```

## Properties

### The slice precategory always has a terminal object

The terminal object in the slice (pre-)category `C/X` is the identity morphism
`id : hom X X`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  terminal-obj-Precategory-Slice-Precategory :
    terminal-obj-Precategory (Slice-Precategory C X)
  pr1 terminal-obj-Precategory-Slice-Precategory = (X , id-hom-Precategory C)
  pr2 terminal-obj-Precategory-Slice-Precategory (A , f) =
    is-contr-equiv
      ( Σ (hom-Precategory C A X) (λ g → f ＝ g))
      ( equiv-tot
        ( λ g → equiv-concat' f (left-unit-law-comp-hom-Precategory C g)))
      ( is-torsorial-Id f)
```

### Products in slice precategories are pullbacks in the original category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) {A X Y : obj-Precategory C}
  (f : hom-Precategory C X A) (g : hom-Precategory C Y A)
  where

  module _
    {W : obj-Precategory C}
    (p₁ : hom-Precategory C W X) (p₂ : hom-Precategory C W Y)
    (p : hom-Precategory C W A)
    (α₁ : p ＝ comp-hom-Precategory C f p₁)
    (α₂ : p ＝ comp-hom-Precategory C g p₂)
    (α : comp-hom-Precategory C f p₁ ＝ comp-hom-Precategory C g p₂)
    where

    map-is-pullback-is-product-Slice-Precategory :
      is-pullback-obj-Precategory C A X Y f g W p₁ p₂ α →
      is-product-obj-Precategory
        (Slice-Precategory C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂)
    map-is-pullback-is-product-Slice-Precategory
      ϕ (Z , .(comp-hom-Precategory C f h₁)) (h₁ , refl) (h₂ , β₂) =
      is-contr-Σ-is-prop c d q σ
      where
      c :
        hom-Precategory
          ( Slice-Precategory C A)
          ( Z , comp-hom-Precategory C f h₁)
          ( W , p)
      pr1 c = pr1 (pr1 (ϕ Z h₁ h₂ β₂))
      pr2 c =
        ( ap
          ( comp-hom-Precategory C f)
          ( inv (pr1 (pr2 (pr1 (ϕ Z h₁ h₂ β₂)))))) ∙
        ( inv (associative-comp-hom-Precategory C f p₁ _) ∙
        ap
          ( λ k → comp-hom-Precategory C k (pr1 (pr1 (ϕ Z h₁ h₂ β₂))))
          ( inv α₁))

      d :
        ( ( comp-hom-Precategory (Slice-Precategory C A) (p₁ , α₁) c) ＝
          ( h₁ , refl)) ×
        ( ( comp-hom-Precategory (Slice-Precategory C A) (p₂ , α₂) c) ＝
          ( h₂ , β₂))
      pr1 d =
        eq-hom-Slice-Precategory C A _ _ (pr1 (pr2 (pr1 (ϕ Z h₁ h₂ β₂))))
      pr2 d =
        eq-hom-Slice-Precategory C A _ _ (pr2 (pr2 (pr1 (ϕ Z h₁ h₂ β₂))))

      q :
        (k :
          hom-Precategory
            ( Slice-Precategory C A)
            ( Z , comp-hom-Precategory C f h₁)
            ( W , p)) →
        is-prop
          ( ( comp-hom-Precategory
              (Slice-Precategory C A) (p₁ , α₁) k ＝ (h₁ , refl)) ×
            ( comp-hom-Precategory
              (Slice-Precategory C A) (p₂ , α₂) k ＝ (h₂ , β₂)))
      q k =
        is-prop-product
          ( is-set-hom-Slice-Precategory C A _ _ _ _)
          ( is-set-hom-Slice-Precategory C A _ _ _ _)

      σ :
        (k :
          hom-Precategory
            ( Slice-Precategory C A)
            ( Z , comp-hom-Precategory C f h₁)
            ( W , p)) →
        ( ( comp-hom-Precategory
            ( Slice-Precategory C A)
            ( p₁ , α₁)
            ( k)) ＝
          ( h₁ , refl)) ×
        ( ( comp-hom-Precategory
            ( Slice-Precategory C A)
            ( p₂ , α₂)
            ( k)) ＝
          ( h₂ , β₂)) →
        c ＝ k
      σ (k , γ) (γ₁ , γ₂) =
        eq-hom-Slice-Precategory C A _ _
          ( ap pr1 (pr2 (ϕ Z h₁ h₂ β₂) (k , (ap pr1 γ₁ , ap pr1 γ₂))))

    map-inv-is-pullback-is-product-Slice-Precategory :
      is-product-obj-Precategory
        (Slice-Precategory C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂) →
      is-pullback-obj-Precategory C A X Y f g W p₁ p₂ α
    map-inv-is-pullback-is-product-Slice-Precategory ψ W' p₁' p₂' α' =
      is-contr-Σ-is-prop k γ q σ
      where
      k : hom-Precategory C W' W
      k =
        pr1
          ( pr1
            ( pr1
              ( ψ
                ( W' , comp-hom-Precategory C f p₁')
                ( p₁' , refl)
                ( p₂' , α'))))

      γ :
        (comp-hom-Precategory C p₁ k ＝ p₁') ×
        (comp-hom-Precategory C p₂ k ＝ p₂')
      pr1 γ =
        ap pr1
          ( pr1
            ( pr2
              ( pr1
                ( ψ
                  ( W' , comp-hom-Precategory C f p₁')
                  ( p₁' , refl)
                  ( p₂' , α')))))
      pr2 γ =
        ap pr1
          ( pr2
            ( pr2
              ( pr1
                ( ψ
                  ( W' , comp-hom-Precategory C f p₁')
                  ( p₁' , refl)
                  ( p₂' , α')))))

      q :
        (k' : hom-Precategory C W' W) →
        is-prop
          (( comp-hom-Precategory C p₁ k' ＝ p₁') ×
          ( comp-hom-Precategory C p₂ k' ＝ p₂'))
      q k' =
        is-prop-product
          ( is-set-hom-Precategory C _ _ _ _)
          ( is-set-hom-Precategory C _ _ _ _)

      σ :
        ( k' : hom-Precategory C W' W) →
        ( γ' :
          ( comp-hom-Precategory C p₁ k' ＝ p₁') ×
          ( comp-hom-Precategory C p₂ k' ＝ p₂')) →
          k ＝ k'
      σ k' (γ₁ , γ₂) =
        ap
          ( pr1 ∘ pr1)
          ( pr2
            ( ψ (W' , comp-hom-Precategory C f p₁') (p₁' , refl) (p₂' , α'))
            ( ( ( k') ,
                ( ( ap (comp-hom-Precategory C f) (inv γ₁)) ∙
                  ( ( inv (associative-comp-hom-Precategory C f p₁ k')) ∙
                    ( ap (λ l → comp-hom-Precategory C l k') (inv α₁))))) ,
              ( eq-hom-Slice-Precategory C A _ _ γ₁) ,
              ( eq-hom-Slice-Precategory C A _ _ γ₂)))

    equiv-is-pullback-is-product-Slice-Precategory :
      is-pullback-obj-Precategory C A X Y f g W p₁ p₂ α ≃
      is-product-obj-Precategory
        (Slice-Precategory C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂)
    equiv-is-pullback-is-product-Slice-Precategory =
      equiv-iff-is-prop
        ( is-prop-is-pullback-obj-Precategory C A X Y f g W p₁ p₂ α)
        ( is-prop-is-product-obj-Precategory
          (Slice-Precategory C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂))
        ( map-is-pullback-is-product-Slice-Precategory)
        ( map-inv-is-pullback-is-product-Slice-Precategory)

  map-pullback-product-Slice-Precategory :
    pullback-obj-Precategory C A X Y f g →
    product-obj-Precategory (Slice-Precategory C A) (X , f) (Y , g)
  pr1 (map-pullback-product-Slice-Precategory (W , p₁ , p₂ , α , q)) =
    (W , comp-hom-Precategory C f p₁)
  pr1 (pr2 (map-pullback-product-Slice-Precategory (W , p₁ , p₂ , α , q))) =
    (p₁ , refl)
  pr1
    ( pr2
      ( pr2 (map-pullback-product-Slice-Precategory (W , p₁ , p₂ , α , q)))) =
    (p₂ , α)
  pr2
    ( pr2
      ( pr2 (map-pullback-product-Slice-Precategory (W , p₁ , p₂ , α , q)))) =
    map-is-pullback-is-product-Slice-Precategory
      p₁ p₂ (comp-hom-Precategory C f p₁) refl α α q

  map-inv-pullback-product-Slice-Precategory :
    product-obj-Precategory (Slice-Precategory C A) (X , f) (Y , g) →
    pullback-obj-Precategory C A X Y f g
  pr1 (map-inv-pullback-product-Slice-Precategory
    ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q)) = Z
  pr1 (pr2 (map-inv-pullback-product-Slice-Precategory
    ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q))) = h₁
  pr1 (pr2 (pr2 (map-inv-pullback-product-Slice-Precategory
    ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q)))) = h₂
  pr1 (pr2 (pr2 (pr2 (map-inv-pullback-product-Slice-Precategory
    ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q))))) = inv β₁ ∙ β₂
  pr2 (pr2 (pr2 (pr2 (map-inv-pullback-product-Slice-Precategory
    ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q))))) =
    map-inv-is-pullback-is-product-Slice-Precategory h₁ h₂ h β₁ β₂
      ( inv β₁ ∙ β₂)
      ( q)

  is-section-map-inv-pullback-product-Slice-Precategory :
    ( map-pullback-product-Slice-Precategory ∘
      map-inv-pullback-product-Slice-Precategory) ~ id
  is-section-map-inv-pullback-product-Slice-Precategory
    ((Z , .(comp-hom-Precategory C f h₁)) , (h₁ , refl) , (h₂ , β₂) , q) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( eq-type-subtype
          ( is-product-prop-Precategory
              ( Slice-Precategory C A)
              ( X , f)
              ( Y , g)
              ( Z , comp-hom-Precategory C f h₁)
              ( h₁ , refl))
          ( refl)))

  is-retraction-map-inv-pullback-product-Slice-Precategory :
    ( map-inv-pullback-product-Slice-Precategory ∘
      map-pullback-product-Slice-Precategory) ~ id
  is-retraction-map-inv-pullback-product-Slice-Precategory
    ( W , p₁ , p₂ , α , q) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
          ( eq-pair-eq-fiber
              ( eq-type-subtype
                  ( λ _ → is-pullback-prop-Precategory C A X Y f g _ _ _ α)
                  ( refl))))

  equiv-pullback-product-Slice-Precategory :
    pullback-obj-Precategory C A X Y f g ≃
    product-obj-Precategory (Slice-Precategory C A) (X , f) (Y , g)
  pr1 equiv-pullback-product-Slice-Precategory =
    map-pullback-product-Slice-Precategory
  pr2 equiv-pullback-product-Slice-Precategory =
    is-equiv-is-invertible
      map-inv-pullback-product-Slice-Precategory
      is-section-map-inv-pullback-product-Slice-Precategory
      is-retraction-map-inv-pullback-product-Slice-Precategory
```

### The slice precategory has a forgetful functor

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  forgetful-functor-Slice-Precategory :
    functor-Precategory (Slice-Precategory C X) C
  pr1 forgetful-functor-Slice-Precategory (Y , f) = Y
  pr1 (pr2 forgetful-functor-Slice-Precategory) (f , pf) = f
  pr1 (pr2 (pr2 forgetful-functor-Slice-Precategory)) g h = refl
  pr2 (pr2 (pr2 forgetful-functor-Slice-Precategory)) x = refl
```
