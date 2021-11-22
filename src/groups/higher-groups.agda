{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module groups.higher-groups where

open import foundations.pointed-maps public

∞-Group : (l : Level) → UU (lsuc l)
∞-Group l = Σ (Pointed-Type l) (λ X → is-path-connected (type-Pointed-Type X))

module _
  {l : Level} (G : ∞-Group l)
  where

  classifying-pointed-type-∞-Group : Pointed-Type l
  classifying-pointed-type-∞-Group = pr1 G

  classifying-type-∞-Group : UU l
  classifying-type-∞-Group =
    type-Pointed-Type classifying-pointed-type-∞-Group

  point-∞-Group : classifying-type-∞-Group
  point-∞-Group =
    pt-Pointed-Type classifying-pointed-type-∞-Group

  is-path-connected-classifying-type-∞-Group :
    is-path-connected classifying-type-∞-Group
  is-path-connected-classifying-type-∞-Group = pr2 G

  mere-eq-classifying-type-∞-Group :
    (X Y : classifying-type-∞-Group) → mere-eq X Y
  mere-eq-classifying-type-∞-Group =
    mere-eq-is-path-connected
      is-path-connected-classifying-type-∞-Group

  type-∞-Group : UU l
  type-∞-Group = Id point-∞-Group point-∞-Group

  unit-∞-Group : type-∞-Group
  unit-∞-Group = refl

  mul-∞-Group : (x y : type-∞-Group) → type-∞-Group
  mul-∞-Group x y = x ∙ y

  assoc-mul-∞-Group :
    (x y z : type-∞-Group) →
    Id (mul-∞-Group (mul-∞-Group x y) z)
       (mul-∞-Group x (mul-∞-Group y z))
  assoc-mul-∞-Group = assoc

  left-unit-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group unit-∞-Group x) x
  left-unit-law-mul-∞-Group x = left-unit

  right-unit-law-mul-∞-Group :
    (y : type-∞-Group) → Id (mul-∞-Group y unit-∞-Group) y
  right-unit-law-mul-∞-Group y = right-unit

  coherence-unit-laws-mul-∞-Group :
    Id ( left-unit-law-mul-∞-Group unit-∞-Group)
       ( right-unit-law-mul-∞-Group unit-∞-Group)
  coherence-unit-laws-mul-∞-Group = refl

  inv-∞-Group : type-∞-Group → type-∞-Group
  inv-∞-Group = inv

  left-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group (inv-∞-Group x) x) unit-∞-Group
  left-inverse-law-mul-∞-Group x = left-inv x

  right-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group x (inv-∞-Group x)) unit-∞-Group
  right-inverse-law-mul-∞-Group x = right-inv x

module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : ∞-Group l2)
  where

  hom-∞-Group : UU (l1 ⊔ l2)
  hom-∞-Group =
    classifying-pointed-type-∞-Group G →* classifying-pointed-type-∞-Group H

  classifying-map-hom-∞-Group :
    hom-∞-Group → classifying-type-∞-Group G → classifying-type-∞-Group H
  classifying-map-hom-∞-Group =
    map-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)

  preserves-point-classifying-map-hom-∞-Group :
    (f : hom-∞-Group) →
    Id (classifying-map-hom-∞-Group f (point-∞-Group G)) (point-∞-Group H)
  preserves-point-classifying-map-hom-∞-Group =
    preserves-point-map-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)

  map-hom-∞-Group : hom-∞-Group → type-∞-Group G → type-∞-Group H
  map-hom-∞-Group f x =
    ( inv (preserves-point-classifying-map-hom-∞-Group f)) ∙
    ( ( ap (classifying-map-hom-∞-Group f) x) ∙
      ( preserves-point-classifying-map-hom-∞-Group f))

  preserves-unit-map-hom-∞-Group :
    (f : hom-∞-Group) → Id (map-hom-∞-Group f (unit-∞-Group G)) (unit-∞-Group H)
  preserves-unit-map-hom-∞-Group f =
    left-inv (preserves-point-classifying-map-hom-∞-Group f)

  preserves-mul-map-hom-∞-Group :
    (f : hom-∞-Group) (x y : type-∞-Group G) →
    Id ( map-hom-∞-Group f (mul-∞-Group G x y))
       ( mul-∞-Group H (map-hom-∞-Group f x) (map-hom-∞-Group f y))
  preserves-mul-map-hom-∞-Group f x y =
    ( ap
      ( concat
        ( inv (preserves-point-classifying-map-hom-∞-Group f))
        ( point-∞-Group H))
      ( ( ap
          ( concat'
            ( classifying-map-hom-∞-Group f (point-∞-Group G))
            ( preserves-point-classifying-map-hom-∞-Group f))
          ( ( ap-concat (classifying-map-hom-∞-Group f) x y) ∙
            ( ( ap
                ( concat
                  ( ap (classifying-map-hom-∞-Group f) x)
                  ( classifying-map-hom-∞-Group f (point-∞-Group G)))
                {! ap ( concat' ? ?) ?!}) ∙
              {!!}))) ∙
        {!!})) ∙
    {!!}
