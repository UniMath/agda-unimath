{-# OPTIONS --without-K --exact-split #-}

module groups.concrete-groups where

open import groups.higher-groups public

Concrete-Group : (l : Level) → UU (lsuc l)
Concrete-Group l = Σ (∞-Group l) (λ G → is-set (type-∞-Group G))

module _
  {l : Level} (G : Concrete-Group l)
  where

  ∞-group-Concrete-Group : ∞-Group l
  ∞-group-Concrete-Group = pr1 G

  classifying-pointed-type-Concrete-Group : UU-pt l
  classifying-pointed-type-Concrete-Group =
    classifying-pointed-type-∞-Group ∞-group-Concrete-Group

  classifying-type-Concrete-Group : UU l
  classifying-type-Concrete-Group =
    classifying-type-∞-Group ∞-group-Concrete-Group

  point-Concrete-Group : classifying-type-Concrete-Group
  point-Concrete-Group =
    point-∞-Group ∞-group-Concrete-Group

  is-path-connected-classifying-type-Concrete-Group :
    is-path-connected classifying-type-Concrete-Group
  is-path-connected-classifying-type-Concrete-Group =
    is-path-connected-classifying-type-∞-Group ∞-group-Concrete-Group

  mere-eq-classifying-type-Concrete-Group :
    (X Y : classifying-type-Concrete-Group) → mere-eq X Y
  mere-eq-classifying-type-Concrete-Group =
    mere-eq-classifying-type-∞-Group ∞-group-Concrete-Group

  type-Concrete-Group : UU l
  type-Concrete-Group = type-∞-Group ∞-group-Concrete-Group

  unit-Concrete-Group : type-Concrete-Group
  unit-Concrete-Group = unit-∞-Group ∞-group-Concrete-Group

  mul-Concrete-Group : (x y : type-Concrete-Group) → type-Concrete-Group
  mul-Concrete-Group = mul-∞-Group ∞-group-Concrete-Group

  assoc-mul-Concrete-Group :
    (x y z : type-Concrete-Group) →
    Id (mul-Concrete-Group (mul-Concrete-Group x y) z)
       (mul-Concrete-Group x (mul-Concrete-Group y z))
  assoc-mul-Concrete-Group = assoc-mul-∞-Group ∞-group-Concrete-Group

  left-unit-law-mul-Concrete-Group :
    (x : type-Concrete-Group) → Id (mul-Concrete-Group unit-Concrete-Group x) x
  left-unit-law-mul-Concrete-Group =
    left-unit-law-mul-∞-Group ∞-group-Concrete-Group

  right-unit-law-mul-Concrete-Group :
    (y : type-Concrete-Group) → Id (mul-Concrete-Group y unit-Concrete-Group) y
  right-unit-law-mul-Concrete-Group =
    right-unit-law-mul-∞-Group ∞-group-Concrete-Group

  coherence-unit-laws-mul-Concrete-Group :
    Id ( left-unit-law-mul-Concrete-Group unit-Concrete-Group)
       ( right-unit-law-mul-Concrete-Group unit-Concrete-Group)
  coherence-unit-laws-mul-Concrete-Group =
    coherence-unit-laws-mul-∞-Group ∞-group-Concrete-Group

  inv-Concrete-Group : type-Concrete-Group → type-Concrete-Group
  inv-Concrete-Group = inv-∞-Group ∞-group-Concrete-Group

  left-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group) →
    Id (mul-Concrete-Group (inv-Concrete-Group x) x) unit-Concrete-Group
  left-inverse-law-mul-Concrete-Group =
    left-inverse-law-mul-∞-Group ∞-group-Concrete-Group

  right-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group) →
    Id (mul-Concrete-Group x (inv-Concrete-Group x)) unit-Concrete-Group
  right-inverse-law-mul-Concrete-Group =
    right-inverse-law-mul-∞-Group ∞-group-Concrete-Group
