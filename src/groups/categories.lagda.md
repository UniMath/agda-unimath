---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.categories where

open import foundations public

-- Categories

module _
  {l1 l2 : Level} {A : UU l1} (hom : A → A → UU-Set l2)
  where
  
  associative-composition-structure-Set : UU (l1 ⊔ l2)
  associative-composition-structure-Set =
    Σ ( {x y z : A}
        → type-Set (hom y z)
        → type-Set (hom x y)
        → type-Set (hom x z))
      ( λ μ →
        {x y z w : A} (h : type-Set (hom z w)) (g : type-Set (hom y z))
        (f : type-Set (hom x y)) →
        Id (μ (μ h g) f) (μ h (μ g f)))

  is-unital-composition-structure-Set :
    associative-composition-structure-Set → UU (l1 ⊔ l2)
  is-unital-composition-structure-Set μ =
    Σ ( (x : A) → type-Set (hom x x))
      ( λ e →
        ( {x y : A} (f : type-Set (hom x y)) → Id (pr1 μ (e y) f) f) ×
        ( {x y : A} (f : type-Set (hom x y)) → Id (pr1 μ f (e x)) f))

  abstract
    all-elements-equal-is-unital-composition-structure-Set :
      ( μ : associative-composition-structure-Set) →
      all-elements-equal (is-unital-composition-structure-Set μ)
    all-elements-equal-is-unital-composition-structure-Set
      ( pair μ assoc-μ)
      ( pair e (pair left-unit-law-e right-unit-law-e))
      ( pair e' (pair left-unit-law-e' right-unit-law-e')) =
      eq-subtype
        ( λ x →
          is-prop-prod
            ( is-prop-Π'
              ( λ a →
                is-prop-Π'
                  ( λ b →
                    is-prop-Π
                      ( λ f' → is-set-type-Set (hom a b) (μ (x b) f') f'))))
            ( is-prop-Π'
              ( λ a →
                is-prop-Π'
                  ( λ b →
                    is-prop-Π
                    ( λ f' →
                      is-set-type-Set (hom a b) (μ f' (x a)) f')))))
        ( eq-htpy
          ( λ x → (inv (left-unit-law-e' (e x))) ∙ right-unit-law-e (e' x)))

    is-prop-is-unital-composition-structure-Set :
      ( μ : associative-composition-structure-Set) →
      is-prop (is-unital-composition-structure-Set μ)
    is-prop-is-unital-composition-structure-Set μ =
      is-prop-all-elements-equal
        ( all-elements-equal-is-unital-composition-structure-Set μ)

Precat :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Precat l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( A → A → UU-Set l2)
        ( λ hom →
          Σ ( associative-composition-structure-Set hom)
            ( is-unital-composition-structure-Set hom)))

module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where
  
  obj-Precat : UU l1
  obj-Precat = pr1 C
  
  hom-Precat-Set : (x y : obj-Precat) → UU-Set l2
  hom-Precat-Set = pr1 (pr2 C)

  hom-Precat : (x y : obj-Precat) → UU l2
  hom-Precat x y = type-Set (hom-Precat-Set x y)

  is-set-hom-Precat : (x y : obj-Precat) → is-set (hom-Precat x y)
  is-set-hom-Precat x y = is-set-type-Set (hom-Precat-Set x y)

  associative-composition-Precat :
    associative-composition-structure-Set hom-Precat-Set
  associative-composition-Precat = pr1 (pr2 (pr2 C))

  comp-Precat :
    {x y z : obj-Precat} → hom-Precat y z → hom-Precat x y → hom-Precat x z
  comp-Precat = pr1 associative-composition-Precat

  comp-Precat' :
    {x y z : obj-Precat} → hom-Precat x y → hom-Precat y z → hom-Precat x z
  comp-Precat' f g = comp-Precat g f

  assoc-comp-Precat :
    {x y z w : obj-Precat} (h : hom-Precat z w) (g : hom-Precat y z)
    (f : hom-Precat x y) →
    Id (comp-Precat (comp-Precat h g) f)
      (comp-Precat h (comp-Precat g f))
  assoc-comp-Precat = pr2 associative-composition-Precat

  is-unital-Precat :
    is-unital-composition-structure-Set
      hom-Precat-Set
      associative-composition-Precat
  is-unital-Precat = pr2 (pr2 (pr2 C))

  id-Precat : (x : obj-Precat) → hom-Precat x x
  id-Precat = pr1 is-unital-Precat

  left-unit-law-Precat :
    {x y : obj-Precat} (f : hom-Precat x y) → Id (comp-Precat (id-Precat y) f) f
  left-unit-law-Precat = pr1 (pr2 is-unital-Precat)

  right-unit-law-Precat :
    {x y : obj-Precat} (f : hom-Precat x y) → Id (comp-Precat f (id-Precat x)) f
  right-unit-law-Precat = pr2 (pr2 is-unital-Precat)

  is-iso-Precat : {x y : obj-Precat} (f : hom-Precat x y) → UU l2
  is-iso-Precat {x} {y} f =
    Σ ( hom-Precat y x)
       ( λ g → Id (comp-Precat f g) (id-Precat y) ×
               Id (comp-Precat g f) (id-Precat x))

  is-proof-irrelevant-is-iso-Precat :
    {x y : obj-Precat} (f : hom-Precat x y) →
    is-proof-irrelevant (is-iso-Precat f)
  pr1 (is-proof-irrelevant-is-iso-Precat f H) = H
  pr2
    ( is-proof-irrelevant-is-iso-Precat {x} {y} f
      ( pair g (pair p q)))
      ( pair g' (pair p' q')) =
    eq-subtype
      ( λ h →
        is-prop-prod
          ( is-set-hom-Precat y y (comp-Precat f h) (id-Precat y))
          ( is-set-hom-Precat x x (comp-Precat h f) (id-Precat x)))
      ( ( inv (right-unit-law-Precat g)) ∙
        ( ( ap (comp-Precat g) (inv p')) ∙
          ( ( inv (assoc-comp-Precat g f g')) ∙
            ( ( ap (comp-Precat' g') q) ∙
              ( left-unit-law-Precat g')))))

  is-prop-is-iso-Precat :
    {x y : obj-Precat} (f : hom-Precat x y) → is-prop (is-iso-Precat f)
  is-prop-is-iso-Precat f =
    is-prop-is-proof-irrelevant (is-proof-irrelevant-is-iso-Precat f)

  iso-Precat : (x y : obj-Precat) → UU l2
  iso-Precat x y = Σ (hom-Precat x y) is-iso-Precat

  iso-Precat-Set : (x y : obj-Precat) → UU-Set l2
  pr1 (iso-Precat-Set x y) = iso-Precat x y
  pr2 (iso-Precat-Set x y) =
    is-set-subtype
      is-prop-is-iso-Precat
      (is-set-hom-Precat x y)

  is-iso-id-Precat : {x : obj-Precat} → is-iso-Precat (id-Precat x)
  pr1 (is-iso-id-Precat {x}) = id-Precat x
  pr1 (pr2 (is-iso-id-Precat {x})) = left-unit-law-Precat (id-Precat x)
  pr2 (pr2 (is-iso-id-Precat {x})) = left-unit-law-Precat (id-Precat x)

  id-iso-Precat : {x : obj-Precat} → iso-Precat x x
  pr1 (id-iso-Precat {x}) = id-Precat x
  pr2 (id-iso-Precat {x}) = is-iso-id-Precat

  iso-eq-Precat : {x y : obj-Precat} → Id x y → iso-Precat x y
  iso-eq-Precat refl = id-iso-Precat

  is-category-Precat-Prop : UU-Prop (l1 ⊔ l2)
  is-category-Precat-Prop =
    Π-Prop obj-Precat
      ( λ x → Π-Prop obj-Precat (λ y → is-equiv-Prop (iso-eq-Precat {x} {y})))

  is-category-Precat : UU (l1 ⊔ l2)
  is-category-Precat = type-Prop is-category-Precat-Prop

Cat : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cat l1 l2 = Σ (Precat l1 l2) is-category-Precat

```
