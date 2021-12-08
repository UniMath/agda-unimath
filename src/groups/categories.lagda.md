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

  composition-Precat :
    {x y z : obj-Precat} → hom-Precat y z → hom-Precat x y → hom-Precat x z
  composition-Precat = pr1 associative-composition-Precat

  assoc-composition-Precat :
    {x y z w : obj-Precat} (h : hom-Precat z w) (g : hom-Precat y z)
    (f : hom-Precat x y) →
    Id (composition-Precat (composition-Precat h g) f)
      (composition-Precat h (composition-Precat g f))
  assoc-composition-Precat = pr2 associative-composition-Precat

  is-unital-Precat :
    is-unital-composition-structure-Set
      hom-Precat-Set
      associative-composition-Precat
  is-unital-Precat = pr2 (pr2 (pr2 C))

{-
id-Precat :
  { l1 l2 : Level} (C : Precat l1 l2) {x : obj-Precat C} →
  hom-Precat C x x
id-Precat (pair A (pair hom (pair (pair μ assoc-μ) t))) {x} =
  pr1 (is-unital-Precat {!!}) x
-}



```
