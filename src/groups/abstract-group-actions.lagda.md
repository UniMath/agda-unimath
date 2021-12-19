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

  Abstract-Group-Action : (l : Level) → UU (l1 ⊔ lsuc l)
  Abstract-Group-Action l =
    Σ (UU-Set l) (λ X → type-hom-Group G (symmetric-Group X))

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  set-Abstract-Group-Action : UU-Set l2
  set-Abstract-Group-Action = pr1 X

  type-Abstract-Group-Action : UU l2
  type-Abstract-Group-Action = type-Set set-Abstract-Group-Action

  is-set-type-Abstract-Group-Action : is-set type-Abstract-Group-Action
  is-set-type-Abstract-Group-Action = is-set-type-Set set-Abstract-Group-Action
  
  equiv-mul-Abstract-Group-Action :
    type-Group G → type-Abstract-Group-Action ≃ type-Abstract-Group-Action
  equiv-mul-Abstract-Group-Action =
    map-hom-Group G (symmetric-Group set-Abstract-Group-Action) (pr2 X)

  mul-Abstract-Group-Action :
    type-Group G → type-Abstract-Group-Action → type-Abstract-Group-Action
  mul-Abstract-Group-Action g =
    map-equiv (equiv-mul-Abstract-Group-Action g)

  preserves-unit-mul-Abstract-Group-Action :
    (mul-Abstract-Group-Action (unit-Group G)) ~ id
  preserves-unit-mul-Abstract-Group-Action =
    htpy-eq
      ( ap pr1
        ( preserves-unit-hom-Group G
          ( symmetric-Group set-Abstract-Group-Action)
          ( pr2 X)))

  preserves-mul-Abstract-Group-Action :
    (g : type-Group G) (h : type-Group G) (x : type-Abstract-Group-Action) →
    Id ( mul-Abstract-Group-Action (mul-Group G g h) x)
       ( mul-Abstract-Group-Action g (mul-Abstract-Group-Action h x))
  preserves-mul-Abstract-Group-Action g h =
    htpy-eq
      ( ap pr1
        ( preserves-mul-hom-Group G
          ( symmetric-Group set-Abstract-Group-Action) (pr2 X) g h))

module _
  {l1 : Level} (G : Group l1)
  where
  
  principal-Abstract-Group-Action : Abstract-Group-Action G l1
  pr1 principal-Abstract-Group-Action = set-Group G
  pr1 (pr2 principal-Abstract-Group-Action) g = equiv-mul-Group G g
  pr2 (pr2 principal-Abstract-Group-Action) g h =
    eq-htpy-equiv (assoc-mul-Group G g h)
  
  conjugation-Abstract-Group-Action : Abstract-Group-Action G l1
  pr1 conjugation-Abstract-Group-Action = set-Group G
  pr1 (pr2 conjugation-Abstract-Group-Action) g = equiv-conjugation-Group G g
  pr2 (pr2 conjugation-Abstract-Group-Action) g h =
    eq-htpy-equiv
      ( λ x →
        ( ap-mul-Group G
          ( assoc-mul-Group G g h x)
          ( distributive-inv-mul-Group G g h)) ∙
        ( ( inv
            ( assoc-mul-Group G
              ( mul-Group G g (mul-Group G h x))
              ( inv-Group G h)
              ( inv-Group G g))) ∙
          ( ap
            ( mul-Group' G (inv-Group G g))
            ( assoc-mul-Group G g
              ( mul-Group G h x)
              ( inv-Group G h)))))

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  type-hom-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  type-hom-Abstract-Group-Action =
    Σ ( type-Set (pr1 X) → type-Set (pr1 Y))
      ( λ f →
        ( g : type-Group G) →
        coherence-square
          ( f)
          ( mul-Abstract-Group-Action G X g)
          ( mul-Abstract-Group-Action G Y g)
          ( f))

  map-hom-Abstract-Group-Action :
    type-hom-Abstract-Group-Action → type-Set (pr1 X) → type-Set (pr1 Y)
  map-hom-Abstract-Group-Action = pr1

  coherence-square-hom-Abstract-Group-Action :
    (f : type-hom-Abstract-Group-Action) (g : type-Group G) →
    coherence-square
      ( map-hom-Abstract-Group-Action f)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( map-hom-Abstract-Group-Action f)
  coherence-square-hom-Abstract-Group-Action = pr2

  is-equiv-hom-Abstract-Group-Action :
    type-hom-Abstract-Group-Action → UU (l2 ⊔ l3)
  is-equiv-hom-Abstract-Group-Action f =
    is-equiv (map-hom-Abstract-Group-Action f)

  equiv-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  equiv-Abstract-Group-Action =
    Σ ( type-Abstract-Group-Action G X ≃ type-Abstract-Group-Action G Y)
      ( λ e →
        ( g : type-Group G) →
        coherence-square
          ( map-equiv e)
          ( mul-Abstract-Group-Action G X g)
          ( mul-Abstract-Group-Action G Y g)
          ( map-equiv e))

  equiv-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action →
    type-Abstract-Group-Action G X ≃ type-Abstract-Group-Action G Y
  equiv-equiv-Abstract-Group-Action = pr1

  map-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action →
    type-Abstract-Group-Action G X → type-Abstract-Group-Action G Y
  map-equiv-Abstract-Group-Action e =
    map-equiv (equiv-equiv-Abstract-Group-Action e)

  is-equiv-map-equiv-Abstract-Group-Action :
    (e : equiv-Abstract-Group-Action) →
    is-equiv (map-equiv-Abstract-Group-Action e)
  is-equiv-map-equiv-Abstract-Group-Action e =
    is-equiv-map-equiv (equiv-equiv-Abstract-Group-Action e)

  coherence-square-equiv-Abstract-Group-Action :
    (e : equiv-Abstract-Group-Action) (g : type-Group G) →
    coherence-square
      ( map-equiv-Abstract-Group-Action e)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( map-equiv-Abstract-Group-Action e)
  coherence-square-equiv-Abstract-Group-Action = pr2

  hom-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action → type-hom-Abstract-Group-Action
  pr1 (hom-equiv-Abstract-Group-Action e) =
    map-equiv-Abstract-Group-Action e
  pr2 (hom-equiv-Abstract-Group-Action e) =
    coherence-square-equiv-Abstract-Group-Action e

  is-equiv-hom-equiv-Abstract-Group-Action :
    (e : equiv-Abstract-Group-Action) →
    is-equiv-hom-Abstract-Group-Action (hom-equiv-Abstract-Group-Action e)
  is-equiv-hom-equiv-Abstract-Group-Action =
    is-equiv-map-equiv-Abstract-Group-Action

  mere-equiv-Abstract-Group-Action-Prop : UU-Prop (l1 ⊔ l2 ⊔ l3)
  mere-equiv-Abstract-Group-Action-Prop =
    trunc-Prop equiv-Abstract-Group-Action

  mere-equiv-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  mere-equiv-Abstract-Group-Action =
    type-Prop mere-equiv-Abstract-Group-Action-Prop

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3) (f : type-hom-Abstract-Group-Action G X Y)
  where

  htpy-hom-Abstract-Group-Action :
    (g : type-hom-Abstract-Group-Action G X Y) → UU (l2 ⊔ l3)
  htpy-hom-Abstract-Group-Action g = pr1 f ~ pr1 g

  refl-htpy-hom-Abstract-Group-Action : htpy-hom-Abstract-Group-Action f
  refl-htpy-hom-Abstract-Group-Action = refl-htpy

  htpy-eq-hom-Abstract-Group-Action :
    (g : type-hom-Abstract-Group-Action G X Y) →
    Id f g → htpy-hom-Abstract-Group-Action g
  htpy-eq-hom-Abstract-Group-Action .f refl =
    refl-htpy-hom-Abstract-Group-Action

  is-contr-total-htpy-hom-Abstract-Group-Action :
    is-contr
      ( Σ ( type-hom-Abstract-Group-Action G X Y)
          ( htpy-hom-Abstract-Group-Action))
  is-contr-total-htpy-hom-Abstract-Group-Action =
    is-contr-total-Eq-substructure
      ( is-contr-total-htpy (pr1 f))
      ( λ g →
        is-prop-Π
          ( λ x →
            is-prop-Π
              ( λ y →
                is-set-type-Set
                  ( set-Abstract-Group-Action G Y)
                  ( g (mul-Abstract-Group-Action G X x y))
                  ( mul-Abstract-Group-Action G Y x (g y)))))
      ( pr1 f)
      ( refl-htpy)
      ( pr2 f)

  is-equiv-htpy-eq-hom-Abstract-Group-Action :
    (g : type-hom-Abstract-Group-Action G X Y) →
    is-equiv (htpy-eq-hom-Abstract-Group-Action g)
  is-equiv-htpy-eq-hom-Abstract-Group-Action =
    fundamental-theorem-id f
      refl-htpy-hom-Abstract-Group-Action
      is-contr-total-htpy-hom-Abstract-Group-Action
      htpy-eq-hom-Abstract-Group-Action

  extensionality-hom-Abstract-Group-Action :
    (g : type-hom-Abstract-Group-Action G X Y) →
    Id f g ≃ htpy-hom-Abstract-Group-Action g
  pr1 (extensionality-hom-Abstract-Group-Action g) =
    htpy-eq-hom-Abstract-Group-Action g
  pr2 (extensionality-hom-Abstract-Group-Action g) =
    is-equiv-htpy-eq-hom-Abstract-Group-Action g

  eq-htpy-hom-Abstract-Group-Action :
    (g : type-hom-Abstract-Group-Action G X Y) →
    htpy-hom-Abstract-Group-Action g → Id f g
  eq-htpy-hom-Abstract-Group-Action g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-Abstract-Group-Action g)

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where
  
  is-set-type-hom-Abstract-Group-Action :
    is-set (type-hom-Abstract-Group-Action G X Y)
  is-set-type-hom-Abstract-Group-Action f g =
    is-prop-equiv
      ( extensionality-hom-Abstract-Group-Action G X Y f g)
      ( is-prop-Π
        ( λ x →
          is-set-type-Abstract-Group-Action G Y
            ( map-hom-Abstract-Group-Action G X Y f x)
            ( map-hom-Abstract-Group-Action G X Y g x)))

  hom-Abstract-Group-Action : UU-Set (l1 ⊔ l2 ⊔ l3)
  pr1 hom-Abstract-Group-Action = type-hom-Abstract-Group-Action G X Y
  pr2 hom-Abstract-Group-Action = is-set-type-hom-Abstract-Group-Action

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  id-hom-Abstract-Group-Action : type-hom-Abstract-Group-Action G X X
  pr1 id-hom-Abstract-Group-Action = id
  pr2 id-hom-Abstract-Group-Action g = refl-htpy

module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3) (Z : Abstract-Group-Action G l4)
  where

  comp-hom-Abstract-Group-Action :
    type-hom-Abstract-Group-Action G Y Z →
    type-hom-Abstract-Group-Action G X Y →
    type-hom-Abstract-Group-Action G X Z
  pr1 (comp-hom-Abstract-Group-Action (pair g K) (pair f H)) = g ∘ f
  pr2 (comp-hom-Abstract-Group-Action (pair g K) (pair f H)) x =
    coherence-square-comp-horizontal
      ( f)
      ( g)
      ( mul-Abstract-Group-Action G X x)
      ( mul-Abstract-Group-Action G Y x)
      ( mul-Abstract-Group-Action G Z x)
      ( f)
      ( g)
      ( H x)
      ( K x)

module _
  {l1 l2 l3 l4 l5 : Level} (G : Group l1) (X1 : Abstract-Group-Action G l2)
  (X2 : Abstract-Group-Action G l3) (X3 : Abstract-Group-Action G l4)
  (X4 : Abstract-Group-Action G l5)
  where

  associative-comp-hom-Abstract-Group-Action :
    (h : type-hom-Abstract-Group-Action G X3 X4)
    (g : type-hom-Abstract-Group-Action G X2 X3)
    (f : type-hom-Abstract-Group-Action G X1 X2) →
    Id ( comp-hom-Abstract-Group-Action G X1 X2 X4
         ( comp-hom-Abstract-Group-Action G X2 X3 X4 h g)
         ( f))
       ( comp-hom-Abstract-Group-Action G X1 X3 X4 h
         ( comp-hom-Abstract-Group-Action G X1 X2 X3 g f))
  associative-comp-hom-Abstract-Group-Action h g f =
    eq-htpy-hom-Abstract-Group-Action G X1 X4
      ( comp-hom-Abstract-Group-Action G X1 X2 X4
        ( comp-hom-Abstract-Group-Action G X2 X3 X4 h g)
        ( f))
      ( comp-hom-Abstract-Group-Action G X1 X3 X4 h
        ( comp-hom-Abstract-Group-Action G X1 X2 X3 g f))
      ( refl-htpy)

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  left-unit-law-comp-hom-Abstract-Group-Action :
    (f : type-hom-Abstract-Group-Action G X Y) →
    Id ( comp-hom-Abstract-Group-Action G X Y Y
         ( id-hom-Abstract-Group-Action G Y)
         ( f))
       ( f)
  left-unit-law-comp-hom-Abstract-Group-Action f =
    eq-htpy-hom-Abstract-Group-Action G X Y
      ( comp-hom-Abstract-Group-Action G X Y Y
        ( id-hom-Abstract-Group-Action G Y)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-hom-Abstract-Group-Action :
    (f : type-hom-Abstract-Group-Action G X Y) →
    Id ( comp-hom-Abstract-Group-Action G X X Y f
         ( id-hom-Abstract-Group-Action G X))
       ( f)
  right-unit-law-comp-hom-Abstract-Group-Action f =
    eq-htpy-hom-Abstract-Group-Action G X Y
      ( comp-hom-Abstract-Group-Action G X X Y f
        ( id-hom-Abstract-Group-Action G X))
      ( f)
      ( refl-htpy)

module _
  {l1 : Level} (G : Group l1)
  where
  
  Abstract-Group-Action-Precat : (l2 : Level) → Precat (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 (Abstract-Group-Action-Precat l2) = Abstract-Group-Action G l2
  pr1 (pr2 (Abstract-Group-Action-Precat l2)) = hom-Abstract-Group-Action G
  pr1 (pr1 (pr2 (pr2 (Abstract-Group-Action-Precat l2)))) {X} {Y} {Z} =
    comp-hom-Abstract-Group-Action G X Y Z
  pr2 (pr1 (pr2 (pr2 (Abstract-Group-Action-Precat l2)))) {X} {Y} {Z} {W} =
    associative-comp-hom-Abstract-Group-Action G X Y Z W
  pr1 (pr2 (pr2 (pr2 (Abstract-Group-Action-Precat l2)))) =
    id-hom-Abstract-Group-Action G
  pr1 (pr2 (pr2 (pr2 (pr2 (Abstract-Group-Action-Precat l2))))) {X} {Y} =
    left-unit-law-comp-hom-Abstract-Group-Action G X Y
  pr2 (pr2 (pr2 (pr2 (pr2 (Abstract-Group-Action-Precat l2))))) {X} {Y} =
    right-unit-law-comp-hom-Abstract-Group-Action G X Y

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3) (e : equiv-Abstract-Group-Action G X Y)
  where
  
  htpy-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) → UU (l2 ⊔ l3)
  htpy-equiv-Abstract-Group-Action f =
    htpy-hom-Abstract-Group-Action G X Y
      ( hom-equiv-Abstract-Group-Action G X Y e)
      ( hom-equiv-Abstract-Group-Action G X Y f)

  refl-htpy-equiv-Abstract-Group-Action : htpy-equiv-Abstract-Group-Action e
  refl-htpy-equiv-Abstract-Group-Action =
    refl-htpy-hom-Abstract-Group-Action G X Y
      ( hom-equiv-Abstract-Group-Action G X Y e)

  htpy-eq-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id e f → htpy-equiv-Abstract-Group-Action f
  htpy-eq-equiv-Abstract-Group-Action .e refl =
    refl-htpy-equiv-Abstract-Group-Action 

  is-contr-total-htpy-equiv-Abstract-Group-Action :
    is-contr
      ( Σ ( equiv-Abstract-Group-Action G X Y)
          ( htpy-equiv-Abstract-Group-Action))
  is-contr-total-htpy-equiv-Abstract-Group-Action =
    is-contr-equiv
      ( Σ ( Σ ( type-hom-Abstract-Group-Action G X Y) (λ f → is-equiv (pr1 f)))
          ( λ f →
            htpy-hom-Abstract-Group-Action G X Y
              ( hom-equiv-Abstract-Group-Action G X Y e)
              ( pr1 f)))
      ( equiv-Σ
        ( λ f →
          htpy-hom-Abstract-Group-Action G X Y
            ( hom-equiv-Abstract-Group-Action G X Y e)
            ( pr1 f))
        ( equiv-right-swap-Σ)
        ( λ { (pair (pair f E) H) → id-equiv}))
      ( is-contr-total-Eq-substructure
        ( is-contr-total-htpy-hom-Abstract-Group-Action G X Y
          ( hom-equiv-Abstract-Group-Action G X Y e))
        ( λ f → is-subtype-is-equiv (pr1 f))
        ( hom-equiv-Abstract-Group-Action G X Y e)
        ( refl-htpy)
        ( is-equiv-map-equiv (pr1 e)))

  is-equiv-htpy-eq-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    is-equiv (htpy-eq-equiv-Abstract-Group-Action f)
  is-equiv-htpy-eq-equiv-Abstract-Group-Action =
    fundamental-theorem-id e
      refl-htpy-equiv-Abstract-Group-Action
      is-contr-total-htpy-equiv-Abstract-Group-Action
      htpy-eq-equiv-Abstract-Group-Action

  extensionality-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id e f ≃ htpy-equiv-Abstract-Group-Action f
  pr1 (extensionality-equiv-Abstract-Group-Action f) =
    htpy-eq-equiv-Abstract-Group-Action f
  pr2 (extensionality-equiv-Abstract-Group-Action f) =
    is-equiv-htpy-eq-equiv-Abstract-Group-Action f

  eq-htpy-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    htpy-equiv-Abstract-Group-Action f → Id e f
  eq-htpy-equiv-Abstract-Group-Action f =
    map-inv-is-equiv (is-equiv-htpy-eq-equiv-Abstract-Group-Action f)

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  inv-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action G X Y → equiv-Abstract-Group-Action G Y X
  pr1 (inv-equiv-Abstract-Group-Action (pair e H)) = inv-equiv e
  pr2 (inv-equiv-Abstract-Group-Action (pair e H)) g =
    coherence-square-inv-horizontal
      ( e)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( e)
      ( H g)

module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : Abstract-Group-Action G l2) (Y : Abstract-Group-Action G l3)
  (Z : Abstract-Group-Action G l4)
  where

  comp-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action G Y Z → equiv-Abstract-Group-Action G X Y →
    equiv-Abstract-Group-Action G X Z
  pr1 (comp-equiv-Abstract-Group-Action (pair f K) (pair e H)) = f ∘e e
  pr2 (comp-equiv-Abstract-Group-Action (pair f K) (pair e H)) g =
    coherence-square-comp-horizontal
      ( map-equiv e)
      ( map-equiv f)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( mul-Abstract-Group-Action G Z g)
      ( map-equiv e)
      ( map-equiv f)
      ( H g)
      ( K g)

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  id-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action G X X
  pr1 id-equiv-Abstract-Group-Action = id-equiv
  pr2 id-equiv-Abstract-Group-Action g = refl-htpy

  equiv-eq-Abstract-Group-Action :
    (Y : Abstract-Group-Action G l2) →
    Id X Y → equiv-Abstract-Group-Action G X Y
  equiv-eq-Abstract-Group-Action .X refl = id-equiv-Abstract-Group-Action

  abstract
    is-contr-total-equiv-Abstract-Group-Action :
      is-contr
        ( Σ ( Abstract-Group-Action G l2)
            ( equiv-Abstract-Group-Action G X))
    is-contr-total-equiv-Abstract-Group-Action =
      is-contr-total-Eq-structure
        ( λ Y ν e →
          (g : type-Group G) →
          htpy-equiv
            ( e ∘e map-hom-Group G (symmetric-Group (pr1 X)) (pr2 X) g)
            ( map-hom-Group G (symmetric-Group Y) ν g ∘e e))
        ( is-contr-total-equiv-Set (pr1 X))
        ( pair (pr1 X) id-equiv)
        ( is-contr-equiv
          ( Σ ( type-hom-Group G (symmetric-Group (pr1 X)))
              ( htpy-hom-Group G (symmetric-Group (pr1 X)) (pr2 X)))
          ( equiv-tot
            ( λ f →
              equiv-map-Π
                ( λ g →
                  inv-equiv
                    ( equiv-htpy-eq-equiv
                      ( map-hom-Group G (symmetric-Group (pr1 X)) (pr2 X) g)
                      ( map-hom-Group G (symmetric-Group (pr1 X)) f g)))))
          ( is-contr-total-htpy-hom-Group G
            ( symmetric-Group (pr1 X))
            ( pr2 X)))

  abstract
    is-equiv-equiv-eq-Abstract-Group-Action :
      (Y : Abstract-Group-Action G l2) →
      is-equiv (equiv-eq-Abstract-Group-Action Y)
    is-equiv-equiv-eq-Abstract-Group-Action =
      fundamental-theorem-id X
        id-equiv-Abstract-Group-Action
        is-contr-total-equiv-Abstract-Group-Action
        equiv-eq-Abstract-Group-Action

  eq-equiv-Abstract-Group-Action :
    (Y : Abstract-Group-Action G l2) →
    equiv-Abstract-Group-Action G X Y → Id X Y
  eq-equiv-Abstract-Group-Action Y =
    map-inv-is-equiv (is-equiv-equiv-eq-Abstract-Group-Action Y)

  extensionality-Abstract-Group-Action :
    (Y : Abstract-Group-Action G l2) →
    Id X Y ≃ equiv-Abstract-Group-Action G X Y
  pr1 (extensionality-Abstract-Group-Action Y) =
    equiv-eq-Abstract-Group-Action Y
  pr2 (extensionality-Abstract-Group-Action Y) =
    is-equiv-equiv-eq-Abstract-Group-Action Y

module _
  {l1 l2 l3 l4 l5 : Level} (G : Group l1) (X1 : Abstract-Group-Action G l2)
  (X2 : Abstract-Group-Action G l3) (X3 : Abstract-Group-Action G l4)
  (X4 : Abstract-Group-Action G l5)
  where

  associative-comp-equiv-Abstract-Group-Action :
    (h : equiv-Abstract-Group-Action G X3 X4)
    (g : equiv-Abstract-Group-Action G X2 X3)
    (f : equiv-Abstract-Group-Action G X1 X2) →
    Id ( comp-equiv-Abstract-Group-Action G X1 X2 X4
         ( comp-equiv-Abstract-Group-Action G X2 X3 X4 h g)
         ( f))
       ( comp-equiv-Abstract-Group-Action G X1 X3 X4 h
         ( comp-equiv-Abstract-Group-Action G X1 X2 X3 g f))
  associative-comp-equiv-Abstract-Group-Action h g f =
    eq-htpy-equiv-Abstract-Group-Action G X1 X4
      ( comp-equiv-Abstract-Group-Action G X1 X2 X4
        ( comp-equiv-Abstract-Group-Action G X2 X3 X4 h g)
        ( f))
      ( comp-equiv-Abstract-Group-Action G X1 X3 X4 h
        ( comp-equiv-Abstract-Group-Action G X1 X2 X3 g f))
      ( refl-htpy)

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  left-unit-law-comp-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id ( comp-equiv-Abstract-Group-Action G X Y Y
         ( id-equiv-Abstract-Group-Action G Y)
         ( f))
       ( f)
  left-unit-law-comp-equiv-Abstract-Group-Action f =
    eq-htpy-equiv-Abstract-Group-Action G X Y
      ( comp-equiv-Abstract-Group-Action G X Y Y
        ( id-equiv-Abstract-Group-Action G Y)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id ( comp-equiv-Abstract-Group-Action G X X Y f
         ( id-equiv-Abstract-Group-Action G X))
       ( f)
  right-unit-law-comp-equiv-Abstract-Group-Action f =
    eq-htpy-equiv-Abstract-Group-Action G X Y
      ( comp-equiv-Abstract-Group-Action G X X Y f
        ( id-equiv-Abstract-Group-Action G X))
      ( f)
      ( refl-htpy)

  left-inverse-law-comp-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id ( comp-equiv-Abstract-Group-Action G X Y X
         ( inv-equiv-Abstract-Group-Action G X Y f)
         ( f))
       ( id-equiv-Abstract-Group-Action G X)
  left-inverse-law-comp-equiv-Abstract-Group-Action f =
    eq-htpy-equiv-Abstract-Group-Action G X X
      ( comp-equiv-Abstract-Group-Action G X Y X
        ( inv-equiv-Abstract-Group-Action G X Y f)
        ( f))
      ( id-equiv-Abstract-Group-Action G X)
      ( isretr-map-inv-equiv (pr1 f))

  right-inverse-law-comp-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id ( comp-equiv-Abstract-Group-Action G Y X Y f
         ( inv-equiv-Abstract-Group-Action G X Y f))
       ( id-equiv-Abstract-Group-Action G Y)
  right-inverse-law-comp-equiv-Abstract-Group-Action f =
    eq-htpy-equiv-Abstract-Group-Action G Y Y
      ( comp-equiv-Abstract-Group-Action G Y X Y f
        ( inv-equiv-Abstract-Group-Action G X Y f))
      ( id-equiv-Abstract-Group-Action G Y)
      ( issec-map-inv-equiv (pr1 f))

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  is-iso-hom-Abstract-Group-Action :
    (f : type-hom-Abstract-Group-Action G X Y) → UU (l1 ⊔ l2 ⊔ l3)
  is-iso-hom-Abstract-Group-Action f =
    Σ ( type-hom-Abstract-Group-Action G Y X)
      ( λ g →
        ( Id ( comp-hom-Abstract-Group-Action G X Y X g f)
             ( id-hom-Abstract-Group-Action G X)) ×
        ( Id ( comp-hom-Abstract-Group-Action G Y X Y f g)
             ( id-hom-Abstract-Group-Action G Y)))

  iso-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  iso-Abstract-Group-Action =
    Σ (type-hom-Abstract-Group-Action G X Y) is-iso-hom-Abstract-Group-Action

  hom-iso-Abstract-Group-Action :
    iso-Abstract-Group-Action → type-hom-Abstract-Group-Action G X Y
  hom-iso-Abstract-Group-Action = pr1

  map-iso-Abstract-Group-Action :
    iso-Abstract-Group-Action →
    type-Abstract-Group-Action G X → type-Abstract-Group-Action G Y
  map-iso-Abstract-Group-Action f =
    map-hom-Abstract-Group-Action G X Y (hom-iso-Abstract-Group-Action f)

  coherence-square-iso-Abstract-Group-Action :
    (f : iso-Abstract-Group-Action) (g : type-Group G) →
    coherence-square
      ( map-iso-Abstract-Group-Action f)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( map-iso-Abstract-Group-Action f)
  coherence-square-iso-Abstract-Group-Action f =
    coherence-square-hom-Abstract-Group-Action G X Y
      ( hom-iso-Abstract-Group-Action f)

  hom-inv-iso-Abstract-Group-Action :
    iso-Abstract-Group-Action → type-hom-Abstract-Group-Action G Y X
  hom-inv-iso-Abstract-Group-Action f = pr1 (pr2 f)

  map-hom-inv-iso-Abstract-Group-Action :
    iso-Abstract-Group-Action →
    type-Abstract-Group-Action G Y → type-Abstract-Group-Action G X
  map-hom-inv-iso-Abstract-Group-Action f =
    map-hom-Abstract-Group-Action G Y X
      ( hom-inv-iso-Abstract-Group-Action f)

  is-iso-hom-iso-Abstract-Group-Action :
    (f : iso-Abstract-Group-Action) →
    is-iso-hom-Abstract-Group-Action (hom-iso-Abstract-Group-Action f)
  is-iso-hom-iso-Abstract-Group-Action = pr2

  equiv-iso-Abstract-Group-Action :
    iso-Abstract-Group-Action → equiv-Abstract-Group-Action G X Y
  pr1 (pr1 (equiv-iso-Abstract-Group-Action f)) =
    map-iso-Abstract-Group-Action f
  pr2 (pr1 (equiv-iso-Abstract-Group-Action f)) =
    is-equiv-has-inverse
      ( map-hom-inv-iso-Abstract-Group-Action f)
      ( htpy-eq-hom-Abstract-Group-Action G Y Y
        ( comp-hom-Abstract-Group-Action G Y X Y
          ( hom-iso-Abstract-Group-Action f)
          ( hom-inv-iso-Abstract-Group-Action f))
        ( id-hom-Abstract-Group-Action G Y)
        ( pr2 (pr2 (pr2 f))))
      ( htpy-eq-hom-Abstract-Group-Action G X X
        ( comp-hom-Abstract-Group-Action G X Y X
          ( hom-inv-iso-Abstract-Group-Action f)
          ( hom-iso-Abstract-Group-Action f))
        ( id-hom-Abstract-Group-Action G X)
        ( pr1 (pr2  (pr2 f))))
  pr2 (equiv-iso-Abstract-Group-Action f) =
    coherence-square-iso-Abstract-Group-Action f

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  -- The following are the morphisms in a groupoid with objects type-Set X
  hom-orbit-Abstract-Group-Action :
    (x y : type-Abstract-Group-Action G X) → UU (l1 ⊔ l2)
  hom-orbit-Abstract-Group-Action x y =
    Σ (type-Group G) (λ g → Id (mul-Abstract-Group-Action G X g x) y)

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  -- The following defines the stabilizer subgroup of G
  type-stabilizer-Abstract-Group-Action :
    type-Abstract-Group-Action G X → UU (l1 ⊔ l2)
  type-stabilizer-Abstract-Group-Action x =
    Σ (type-Group G) (λ g → Id (mul-Abstract-Group-Action G X g x) x)
```
