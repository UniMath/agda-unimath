---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.abstract-group-actions where

open import groups.abstract-groups public

module _
  {l1 : Level} (G : Group l1)
  where

  action-Abstract-Group : {l2 : Level} (X : UU-Set l2) → UU (l1 ⊔ l2)
  action-Abstract-Group X = hom-Group G (symmetric-Group X)

module _
  {l1 l2 : Level} (G : Group l1) (X : UU-Set l2) (μ : action-Abstract-Group G X)
  where
  
  equiv-mul-action-Abstract-Group : type-Group G → type-Set X ≃ type-Set X
  equiv-mul-action-Abstract-Group = map-hom-Group G (symmetric-Group X) μ

  mul-action-Abstract-Group : type-Group G → type-Set X → type-Set X
  mul-action-Abstract-Group g =
    map-equiv (equiv-mul-action-Abstract-Group g)

  preserves-unit-mul-action-Abstract-Group :
    (mul-action-Abstract-Group (unit-Group G)) ~ id
  preserves-unit-mul-action-Abstract-Group =
    htpy-eq (ap pr1 (preserves-unit-hom-Group G (symmetric-Group X) μ))

  preserves-mul-action-Abstract-Group :
    (g : type-Group G) (h : type-Group G) (x : type-Set X) →
    Id ( mul-action-Abstract-Group (mul-Group G g h) x)
       ( mul-action-Abstract-Group g (mul-action-Abstract-Group h x))
  preserves-mul-action-Abstract-Group g h =
    htpy-eq (ap pr1 (preserves-mul-hom-Group G (symmetric-Group X) μ g h))

module _
  {l1 : Level} (G : Group l1)
  where
  
  principal-action-Abstract-Group : action-Abstract-Group G (set-Group G)
  pr1 principal-action-Abstract-Group g = equiv-mul-Group G g
  pr2 principal-action-Abstract-Group g h =
    eq-htpy-equiv (is-associative-mul-Group G g h)

  conjugation-action-Abstract-Group : action-Abstract-Group G (set-Group G)
  pr1 conjugation-action-Abstract-Group g = equiv-conjugation-Group G g
  pr2 conjugation-action-Abstract-Group g h =
    eq-htpy-equiv
      ( λ x →
        ( ap-mul-Group G
          ( is-associative-mul-Group G g h x)
          ( distributive-inv-mul-Group G g h)) ∙
        ( ( inv
            ( is-associative-mul-Group G
              ( mul-Group G g (mul-Group G h x))
              ( inv-Group G h)
              ( inv-Group G g))) ∙
          ( ap
            ( mul-Group' G (inv-Group G g))
            ( is-associative-mul-Group G g
              ( mul-Group G h x)
              ( inv-Group G h)))))

```
