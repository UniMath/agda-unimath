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
      (eq-htpy
        ( λ x → (inv (left-unit-law-e' (e x))) ∙ right-unit-law-e (e' x)))

-- Precategory :
--   (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
-- Precategory l1 l2 =
--   Σ ( UU l1) (λ A →
--     Σ (A → A → UU-Set l2) (λ hom →
--       Σ ( associative-composition-structure A hom)
--         ( is-unital-composition-structure A hom)))

-- obj-Precat :
--   {l1 l2 : Level} → Precategory l1 l2 → UU l1
-- obj-Precat C = pr1 C

-- hom-Set-Precat :
--   {l1 l2 : Level} (C : Precategory l1 l2) (x y : obj-Precat C) → UU-Set l2
-- hom-Set-Precat C = pr1 (pr2 C)

-- hom-Precat :
--   {l1 l2 : Level} (C : Precategory l1 l2) (x y : obj-Precat C) → UU l2
-- hom-Precat C x y = pr1 (hom-Set-Precat C x y)

-- is-set-hom-Precat :
--   {l1 l2 : Level} (C : Precategory l1 l2) (x y : obj-Precat C) →
--   is-set (hom-Precat C x y)
-- is-set-hom-Precat C x y = pr2 (hom-Set-Precat C x y)

-- associative-composition-Precat :
--   {l1 l2 : Level} (C : Precategory l1 l2) →
--   associative-composition-structure (obj-Precat C) (hom-Set-Precat C)
-- associative-composition-Precat C = pr1 (pr2 (pr2 C))

-- composition-Precat :
--   {l1 l2 : Level} (C : Precategory l1 l2) {x y z : obj-Precat C} →
--   hom-Precat C x y → hom-Precat C y z → hom-Precat C x z
-- composition-Precat C {x} {y} {z} =
--   pr1 (associative-composition-Precat C) x y z

-- assoc-composition-Precat :
--   { l1 l2 : Level} (C : Precategory l1 l2) {x y z w : obj-Precat C} →
--   ( f : hom-Precat C x y) (g : hom-Precat C y z) (h : hom-Precat C z w) →
--   Id (composition-Precat C (composition-Precat C f g) h)
--      (composition-Precat C f (composition-Precat C g h))
-- assoc-composition-Precat C {x} {y} {z} {w} =
--   pr2 (associative-composition-Precat C) x y z w

-- is-unital-Precat :
--   { l1 l2 : Level} (C : Precategory l1 l2) →
--   is-unital-composition-structure
--     ( obj-Precat C)
--     ( hom-Set-Precat C)
--     ( associative-composition-Precat C)
-- is-unital-Precat C = pr2 (pr2 (pr2 C))

-- {-
-- id-Precat :
--   { l1 l2 : Level} (C : Precategory l1 l2) {x : obj-Precat C} →
--   hom-Precat C x x
-- id-Precat (pair A (pair hom (pair (pair μ assoc-μ) t))) {x} =
--   pr1 (is-unital-Precat {!!}) x
-- -}



-- ```
