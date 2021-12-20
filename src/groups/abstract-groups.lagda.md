---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.abstract-groups where

open import categories public

--------------------------------------------------------------------------------

-- Groups in univalent mathematics

--------------------------------------------------------------------------------

{- We first introduce semigroups, and then groups. We do this because the
   category of groups is a full subcategory of the category of semigroups.
   In particular, it is a proposition for a semigroup to be a group. Therefore
   this approach gives us in a straightforward way that equality of groups is 
   equality of semigroups. This will be useful in showing that group 
   isomorphisms are equivalent to identifications of groups. -}

has-associative-mul : {l : Level} (X : UU l) → UU l
has-associative-mul X =
  Σ (X → X → X) (λ μ → (x y z : X) → Id (μ (μ x y) z) (μ x (μ y z)))

has-associative-mul-Set :
  {l : Level} (X : UU-Set l) → UU l
has-associative-mul-Set X =
  has-associative-mul (type-Set X)

Semigroup :
  (l : Level) → UU (lsuc l)
Semigroup l = Σ (UU-Set l) has-associative-mul-Set

module _
  {l : Level} (G : Semigroup l)
  where

  set-Semigroup : UU-Set l
  set-Semigroup = pr1 G

  type-Semigroup : UU l
  type-Semigroup = type-Set set-Semigroup

  is-set-type-Semigroup : is-set type-Semigroup
  is-set-type-Semigroup = is-set-type-Set set-Semigroup

  associative-mul-Semigroup : has-associative-mul type-Semigroup
  associative-mul-Semigroup = pr2 G

  mul-Semigroup : type-Semigroup → type-Semigroup → type-Semigroup
  mul-Semigroup = pr1 associative-mul-Semigroup

  assoc-mul-Semigroup :
    (x y z : type-Semigroup) →
    Id ( mul-Semigroup (mul-Semigroup x y) z)
       ( mul-Semigroup x (mul-Semigroup y z))
  assoc-mul-Semigroup = pr2 associative-mul-Semigroup

{- Now we introduce homomorphisms of semigroups. Group homomorphisms are just
    homomorphisms between their underlying semigroups. -}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  preserves-mul : (μA : A → A → A) (μB : B → B → B) → (A → B) → UU (l1 ⊔ l2)
  preserves-mul μA μB f = (x y : A) → Id (f (μA x y)) (μB (f x) (f y))

  preserves-mul-equiv :
    (μA : A → A → A) (μB : B → B → B) → (A ≃ B) → UU (l1 ⊔ l2)
  preserves-mul-equiv μA μB e = preserves-mul μA μB (map-equiv e)

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where
  
  preserves-mul-Semigroup :
    (type-Semigroup G → type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-Semigroup f =
    preserves-mul (mul-Semigroup G) (mul-Semigroup H) f

  preserves-mul-equiv-Semigroup :
    (type-Semigroup G ≃ type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-equiv-Semigroup e =
    preserves-mul-equiv (mul-Semigroup G) (mul-Semigroup H) e

  abstract
    is-prop-preserves-mul-Semigroup :
      ( f : type-Semigroup G → type-Semigroup H) →
      is-prop (preserves-mul-Semigroup f)
    is-prop-preserves-mul-Semigroup f =
      is-prop-Π (λ x →
        is-prop-Π (λ y →
          is-set-type-Semigroup H
            ( f (mul-Semigroup G x y))
            ( mul-Semigroup H (f x) (f y))))

  type-hom-Semigroup : UU (l1 ⊔ l2)
  type-hom-Semigroup =
    Σ ( type-Semigroup G → type-Semigroup H)
      ( preserves-mul-Semigroup)

  map-hom-Semigroup :
    type-hom-Semigroup → type-Semigroup G → type-Semigroup H
  map-hom-Semigroup f = pr1 f

  preserves-mul-hom-Semigroup :
    (f : type-hom-Semigroup) → preserves-mul-Semigroup (map-hom-Semigroup f)
  preserves-mul-hom-Semigroup f = pr2 f

  {- We characterize the identity type of the semigroup homomorphisms. -}

  htpy-hom-Semigroup : (f g : type-hom-Semigroup) → UU (l1 ⊔ l2)
  htpy-hom-Semigroup f g = map-hom-Semigroup f ~ map-hom-Semigroup g

  refl-htpy-hom-Semigroup : (f : type-hom-Semigroup) → htpy-hom-Semigroup f f
  refl-htpy-hom-Semigroup f = refl-htpy

  htpy-eq-hom-Semigroup :
    (f g : type-hom-Semigroup) → Id f g → htpy-hom-Semigroup f g
  htpy-eq-hom-Semigroup f .f refl = refl-htpy-hom-Semigroup f 

  abstract
    is-contr-total-htpy-hom-Semigroup :
      (f : type-hom-Semigroup) →
      is-contr (Σ type-hom-Semigroup (htpy-hom-Semigroup f))
    is-contr-total-htpy-hom-Semigroup f =
      is-contr-total-Eq-substructure
        ( is-contr-total-htpy (map-hom-Semigroup f))
        ( is-prop-preserves-mul-Semigroup)
        ( map-hom-Semigroup f)
        ( refl-htpy)
        ( preserves-mul-hom-Semigroup f)

  abstract
    is-equiv-htpy-eq-hom-Semigroup :
      (f g : type-hom-Semigroup) → is-equiv (htpy-eq-hom-Semigroup f g)
    is-equiv-htpy-eq-hom-Semigroup f =
      fundamental-theorem-id f
        ( refl-htpy-hom-Semigroup f)
        ( is-contr-total-htpy-hom-Semigroup f)
        ( htpy-eq-hom-Semigroup f)

  eq-htpy-hom-Semigroup :
    {f g : type-hom-Semigroup} → htpy-hom-Semigroup f g → Id f g
  eq-htpy-hom-Semigroup {f} {g} =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-Semigroup f g)

  is-set-type-hom-Semigroup : is-set type-hom-Semigroup
  is-set-type-hom-Semigroup f g =
    is-prop-is-equiv
      ( is-equiv-htpy-eq-hom-Semigroup f g)
      ( is-prop-Π
        ( λ x →
          is-set-type-Semigroup H
            ( map-hom-Semigroup f x)
            ( map-hom-Semigroup g x)))

  hom-Semigroup : UU-Set (l1 ⊔ l2)
  pr1 hom-Semigroup = type-hom-Semigroup
  pr2 hom-Semigroup = is-set-type-hom-Semigroup

{- We construct the category of semigroups -}

preserves-mul-id-Semigroup :
  {l : Level} (G : Semigroup l) → preserves-mul-Semigroup G G id
preserves-mul-id-Semigroup (pair (pair G is-set-G) (pair μ-G assoc-G)) x y = refl

id-hom-Semigroup :
  {l : Level} (G : Semigroup l) → type-hom-Semigroup G G
pr1 (id-hom-Semigroup G) = id
pr2 (id-hom-Semigroup G) = preserves-mul-id-Semigroup G

comp-hom-Semigroup :
  {l1 l2 l3 : Level} →
  (G : Semigroup l1) (H : Semigroup l2) (K : Semigroup l3) →
  type-hom-Semigroup H K → type-hom-Semigroup G H → type-hom-Semigroup G K
pr1 (comp-hom-Semigroup G H K g f) =
  (map-hom-Semigroup H K g) ∘ (map-hom-Semigroup G H f)
pr2 (comp-hom-Semigroup G H K g f) x y =
  ( ap ( map-hom-Semigroup H K g)
       ( preserves-mul-hom-Semigroup G H f x y)) ∙
  ( preserves-mul-hom-Semigroup H K g
    ( map-hom-Semigroup G H f x)
    ( map-hom-Semigroup G H f y))

{- Next, we prove the that the laws for a category hold for group homomorphisms,
   i.e., we show that composition is associative and satisfies the left and
   right unit laws. Before we show that these laws hold, we will characterize
   the identity type of the types of semigroup homomorphisms and group 
   homomorphisms. -}

associative-comp-hom-Semigroup :
  { l1 l2 l3 l4 : Level} (G : Semigroup l1) (H : Semigroup l2)
  ( K : Semigroup l3) (L : Semigroup l4) (h : type-hom-Semigroup K L) →
  ( g : type-hom-Semigroup H K) (f : type-hom-Semigroup G H) →
  Id ( comp-hom-Semigroup G H L
       ( comp-hom-Semigroup H K L h g) f)
     ( comp-hom-Semigroup G K L h
       ( comp-hom-Semigroup G H K g f))
associative-comp-hom-Semigroup G H K L (pair h μ-h) (pair g μ-g) (pair f μ-f) =
  eq-htpy-hom-Semigroup G L refl-htpy

left-unit-law-comp-hom-Semigroup :
  { l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  ( f : type-hom-Semigroup G H) →
  Id ( comp-hom-Semigroup G H H (id-hom-Semigroup H) f) f
left-unit-law-comp-hom-Semigroup G
  (pair (pair H is-set-H) (pair μ-H assoc-H)) (pair f μ-f) =
  eq-htpy-hom-Semigroup G
    ( pair (pair H is-set-H) (pair μ-H assoc-H))
    ( refl-htpy)

right-unit-law-comp-hom-Semigroup :
  { l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  ( f : type-hom-Semigroup G H) →
  Id ( comp-hom-Semigroup G G H f (id-hom-Semigroup G)) f
right-unit-law-comp-hom-Semigroup
  (pair (pair G is-set-G) (pair μ-G assoc-G)) H (pair f μ-f) =
  eq-htpy-hom-Semigroup
    ( pair (pair G is-set-G) (pair μ-G assoc-G)) H refl-htpy

Semigroup-Large-Precat : Large-Precat
obj-Large-Precat Semigroup-Large-Precat = Semigroup
hom-Large-Precat Semigroup-Large-Precat = hom-Semigroup
comp-hom-Large-Precat Semigroup-Large-Precat = comp-hom-Semigroup
id-hom-Large-Precat Semigroup-Large-Precat = id-hom-Semigroup
associative-comp-hom-Large-Precat Semigroup-Large-Precat =
  associative-comp-hom-Semigroup
left-unit-law-comp-hom-Large-Precat Semigroup-Large-Precat =
  left-unit-law-comp-hom-Semigroup
right-unit-law-comp-hom-Large-Precat Semigroup-Large-Precat =
  right-unit-law-comp-hom-Semigroup

{- We show that the precategory of semigroups is a category -}

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where
  
  is-iso-hom-Semigroup : (f : type-hom-Semigroup G H) → UU (l1 ⊔ l2)
  is-iso-hom-Semigroup f = is-iso-hom-Large-Precat Semigroup-Large-Precat G H f

  inv-is-iso-hom-Semigroup :
    (f : type-hom-Semigroup G H) →
    is-iso-hom-Semigroup f → type-hom-Semigroup H G
  inv-is-iso-hom-Semigroup f = pr1

  type-iso-Semigroup : UU (l1 ⊔ l2)
  type-iso-Semigroup = type-iso-Large-Precat Semigroup-Large-Precat G H
  
  hom-iso-Semigroup : type-iso-Semigroup → type-hom-Semigroup G H
  hom-iso-Semigroup = hom-iso-Large-Precat Semigroup-Large-Precat G H

  is-iso-hom-iso-Semigroup :
    (f : type-iso-Semigroup) → is-iso-hom-Semigroup (hom-iso-Semigroup f)
  is-iso-hom-iso-Semigroup =
    is-iso-hom-iso-Large-Precat Semigroup-Large-Precat G H

  hom-inv-iso-Semigroup : type-iso-Semigroup → type-hom-Semigroup H G
  hom-inv-iso-Semigroup = hom-inv-iso-Large-Precat Semigroup-Large-Precat G H

  issec-hom-inv-iso-Semigroup :
    (f : type-iso-Semigroup) →
    Id ( comp-hom-Semigroup H G H
         ( hom-iso-Semigroup f)
         ( hom-inv-iso-Semigroup f))
       ( id-hom-Semigroup H)
  issec-hom-inv-iso-Semigroup =
    issec-hom-inv-iso-Large-Precat Semigroup-Large-Precat G H

  isretr-hom-inv-iso-Semigroup :
    (f : type-iso-Semigroup) →
    Id ( comp-hom-Semigroup G H G
         ( hom-inv-iso-Semigroup f)
         ( hom-iso-Semigroup f))
       ( id-hom-Semigroup G)
  isretr-hom-inv-iso-Semigroup =
    isretr-hom-inv-iso-Large-Precat Semigroup-Large-Precat G H

  abstract
    is-prop-is-iso-hom-Semigroup :
      (f : type-hom-Semigroup G H) → is-prop (is-iso-hom-Semigroup f)
    is-prop-is-iso-hom-Semigroup =
      is-prop-is-iso-hom-Large-Precat Semigroup-Large-Precat G H

  abstract
    preserves-mul-map-inv-is-equiv-Semigroup :
      ( f : type-hom-Semigroup G H)
      ( is-equiv-f : is-equiv (map-hom-Semigroup G H f)) →
      preserves-mul-Semigroup H G (map-inv-is-equiv is-equiv-f)
    preserves-mul-map-inv-is-equiv-Semigroup (pair f μ-f) is-equiv-f x y =
      map-inv-is-equiv
        ( is-emb-is-equiv is-equiv-f
          ( map-inv-is-equiv is-equiv-f (mul-Semigroup H x y))
          ( mul-Semigroup G
            ( map-inv-is-equiv is-equiv-f x)
            ( map-inv-is-equiv is-equiv-f y)))
        ( ( ( issec-map-inv-is-equiv is-equiv-f (mul-Semigroup H x y)) ∙
            ( ( ap ( λ t → mul-Semigroup H t y)
                   ( inv (issec-map-inv-is-equiv is-equiv-f x))) ∙
              ( ap
                ( mul-Semigroup H (f (map-inv-is-equiv is-equiv-f x)))
                ( inv (issec-map-inv-is-equiv is-equiv-f y))))) ∙
          ( inv
            ( μ-f
              ( map-inv-is-equiv is-equiv-f x)
              ( map-inv-is-equiv is-equiv-f y))))

  abstract
    is-iso-is-equiv-hom-Semigroup :
      (f : type-hom-Semigroup G H) → is-equiv (pr1 f) → is-iso-hom-Semigroup f
    pr1 (pr1 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      map-inv-is-equiv is-equiv-f
    pr2 (pr1 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      preserves-mul-map-inv-is-equiv-Semigroup (pair f μ-f) is-equiv-f
    pr1 (pr2 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      eq-htpy-hom-Semigroup H H (issec-map-inv-is-equiv is-equiv-f)
    pr2 (pr2 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      eq-htpy-hom-Semigroup G G (isretr-map-inv-is-equiv is-equiv-f)         

  abstract
    is-equiv-is-iso-hom-Semigroup :
      (f : type-hom-Semigroup G H) → is-iso-hom-Semigroup f → is-equiv (pr1 f)
    is-equiv-is-iso-hom-Semigroup
      ( pair f μ-f)
      ( pair (pair g μ-g) (pair issec isretr)) =
      is-equiv-has-inverse g
        ( htpy-eq (ap pr1 issec))
        ( htpy-eq (ap pr1 isretr))

  equiv-Semigroup : UU (l1 ⊔ l2)
  equiv-Semigroup =
    Σ ( type-Semigroup G ≃ type-Semigroup H)
      ( preserves-mul-equiv-Semigroup G H)

  equiv-iso-equiv-Semigroup : equiv-Semigroup ≃ type-iso-Semigroup
  equiv-iso-equiv-Semigroup =
    ( equiv-total-subtype
      ( λ f → is-subtype-is-equiv (map-hom-Semigroup G H f))
      ( is-prop-is-iso-hom-Semigroup)
      ( is-iso-is-equiv-hom-Semigroup)
      ( is-equiv-is-iso-hom-Semigroup)) ∘e
    ( equiv-right-swap-Σ)

module _
  {l : Level} (G : Semigroup l)
  where
  
  center-total-preserves-mul-id-Semigroup :
    Σ ( has-associative-mul (type-Semigroup G))
      ( λ μ → preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)
  pr1 (pr1 (center-total-preserves-mul-id-Semigroup)) = mul-Semigroup G
  pr2 (pr1 (center-total-preserves-mul-id-Semigroup)) = assoc-mul-Semigroup G
  pr2 (center-total-preserves-mul-id-Semigroup) x y = refl

  contraction-total-preserves-mul-id-Semigroup :
    ( t : Σ ( has-associative-mul (type-Semigroup G))
            ( λ μ →
              preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)) →
    Id center-total-preserves-mul-id-Semigroup t
  contraction-total-preserves-mul-id-Semigroup
    (pair (pair μ-G' assoc-G') μ-id) =
    eq-subtype
      ( λ μ →
        is-prop-preserves-mul-Semigroup G
          ( pair (pair (type-Semigroup G) (is-set-type-Semigroup G)) μ) id)
      ( eq-subtype
        ( λ μ →
          is-prop-Π (λ x →
            is-prop-Π (λ y →
              is-prop-Π (λ z →
                is-set-type-Semigroup G (μ (μ x y) z) (μ x (μ y z))))))
        ( eq-htpy (λ x → eq-htpy (λ y → μ-id x y))))

  is-contr-total-preserves-mul-id-Semigroup :
    is-contr
      ( Σ ( has-associative-mul (type-Semigroup G))
          ( λ μ → preserves-mul (mul-Semigroup G) (pr1 μ) id))
  pr1 is-contr-total-preserves-mul-id-Semigroup =
    center-total-preserves-mul-id-Semigroup
  pr2 is-contr-total-preserves-mul-id-Semigroup =
    contraction-total-preserves-mul-id-Semigroup

  is-contr-total-equiv-Semigroup :
    is-contr (Σ (Semigroup l) (equiv-Semigroup G))
  is-contr-total-equiv-Semigroup =
    is-contr-total-Eq-structure
      ( λ H μH → preserves-mul-equiv-Semigroup G (pair H μH))
      ( is-contr-total-Eq-substructure
        ( is-contr-total-equiv (type-Semigroup G))
        ( is-prop-is-set)
        ( type-Semigroup G)
        ( id-equiv)
        ( is-set-type-Semigroup G))
      ( pair (set-Semigroup G) id-equiv)
      ( is-contr-total-preserves-mul-id-Semigroup)

  is-contr-total-iso-Semigroup :
    is-contr (Σ (Semigroup l) (type-iso-Semigroup G))
  is-contr-total-iso-Semigroup =
    is-contr-equiv'
      ( Σ (Semigroup l) (equiv-Semigroup G))
      ( equiv-tot (equiv-iso-equiv-Semigroup G))
      ( is-contr-total-equiv-Semigroup)

  id-iso-Semigroup : type-iso-Semigroup G G
  id-iso-Semigroup = id-iso-Large-Precat Semigroup-Large-Precat G

  iso-eq-Semigroup : (H : Semigroup l) → Id G H → type-iso-Semigroup G H
  iso-eq-Semigroup = iso-eq-Large-Precat Semigroup-Large-Precat G

is-category-Semigroup :
  is-category-Large-Precat Semigroup-Large-Precat
is-category-Semigroup G =
  fundamental-theorem-id G
    ( id-iso-Semigroup G)
    ( is-contr-total-iso-Semigroup G)
    ( iso-eq-Semigroup G)

extensionality-Semigroup :
  {l : Level} (G H : Semigroup l) → Id G H ≃ type-iso-Semigroup G H
pr1 (extensionality-Semigroup G H) = iso-eq-Semigroup G H
pr2 (extensionality-Semigroup G H) = is-category-Semigroup G H

eq-iso-Semigroup :
  {l : Level} (G H : Semigroup l) → type-iso-Semigroup G H → Id G H
eq-iso-Semigroup G H = map-inv-is-equiv (is-category-Semigroup G H)

Semigroup-Large-Cat : Large-Cat
precat-Large-Cat Semigroup-Large-Cat = Semigroup-Large-Precat
is-category-Large-Cat Semigroup-Large-Cat = is-category-Semigroup

--------------------------------------------------------------------------------

{- A semigroup is a monoid if it possesses a unit satisfying unit laws. -}

is-unital :
  {l : Level} → Semigroup l → UU l
is-unital G =
  Σ ( type-Semigroup G)
    ( λ e →
      ( (y : type-Semigroup G) → Id (mul-Semigroup G e y) y) ×
      ( (x : type-Semigroup G) → Id (mul-Semigroup G x e) x))

Monoid :
  (l : Level) → UU (lsuc l)
Monoid l = Σ (Semigroup l) is-unital

semigroup-Monoid :
  {l : Level} (M : Monoid l) → Semigroup l
semigroup-Monoid M = pr1 M

type-Monoid :
  {l : Level} (M : Monoid l) → UU l
type-Monoid M = type-Semigroup (semigroup-Monoid M)

is-set-type-Monoid :
  {l : Level} (M : Monoid l) → is-set (type-Monoid M)
is-set-type-Monoid M = is-set-type-Semigroup (semigroup-Monoid M)

mul-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M → type-Monoid M → type-Monoid M
mul-Monoid M = mul-Semigroup (semigroup-Monoid M)

mul-Monoid' :
  {l : Level} (M : Monoid l) → type-Monoid M → type-Monoid M → type-Monoid M
mul-Monoid' M y x = mul-Monoid M x y

assoc-mul-Monoid :
  {l : Level} (M : Monoid l) (x y z : type-Monoid M) →
  Id (mul-Monoid M (mul-Monoid M x y) z) (mul-Monoid M x (mul-Monoid M y z))
assoc-mul-Monoid M =
  assoc-mul-Semigroup (semigroup-Monoid M)

unit-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M
unit-Monoid M = pr1 (pr2 M)

left-unit-law-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  Id (mul-Monoid M (unit-Monoid M) x) x
left-unit-law-Monoid M = pr1 (pr2 (pr2 M))

right-unit-law-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  Id (mul-Monoid M x (unit-Monoid M)) x
right-unit-law-Monoid M = pr2 (pr2 (pr2 M))

{- We show that is-unital is a proposition. -}

abstract
  all-elements-equal-is-unital :
    {l : Level} (G : Semigroup l) → all-elements-equal (is-unital G)
  all-elements-equal-is-unital (pair (pair X is-set-X) (pair μ assoc-μ))
    (pair e (pair left-unit-e right-unit-e))
    (pair e' (pair left-unit-e' right-unit-e')) =
    eq-subtype
      ( λ e → is-prop-prod
        ( is-prop-Π (λ y → is-set-X (μ e y) y))
        ( is-prop-Π (λ x → is-set-X (μ x e) x)))
      ( (inv (left-unit-e' e)) ∙ (right-unit-e e'))

abstract
  is-prop-is-unital :
    {l : Level} (G : Semigroup l) → is-prop (is-unital G)
  is-prop-is-unital G =
    is-prop-all-elements-equal (all-elements-equal-is-unital G)

is-unital-Prop : {l : Level} (G : Semigroup l) → UU-Prop l
pr1 (is-unital-Prop G) = is-unital G
pr2 (is-unital-Prop G) = is-prop-is-unital G

{- We introduce monoid homomorphisms. -}

preserves-unit-hom-Semigroup :
  { l1 l2 : Level} (M1 : Monoid l1) (M2 : Monoid l2) →
  ( type-hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2)) → UU l2
preserves-unit-hom-Semigroup M1 M2 f =
  Id ( map-hom-Semigroup
       ( semigroup-Monoid M1)
       ( semigroup-Monoid M2)
       ( f)
       ( unit-Monoid M1))
     ( unit-Monoid M2)

hom-Monoid :
  { l1 l2 : Level} (M1 : Monoid l1) (M2 : Monoid l2) → UU (l1 ⊔ l2)
hom-Monoid M1 M2 =
  Σ ( type-hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2))
    ( preserves-unit-hom-Semigroup M1 M2)

preserves-unit-id-hom-Monoid :
  { l : Level} (M : Monoid l) →
  preserves-unit-hom-Semigroup M M (id-hom-Semigroup (semigroup-Monoid M))
preserves-unit-id-hom-Monoid M = refl

id-hom-Monoid :
  {l : Level} (M : Monoid l) → hom-Monoid M M
pr1 (id-hom-Monoid M) = id-hom-Semigroup (semigroup-Monoid M)
pr2 (id-hom-Monoid M) = preserves-unit-id-hom-Monoid M

{- Invertible elements in monoids -}

module _
  {l : Level} (M : Monoid l)
  where

  is-invertible-Monoid : type-Monoid M → UU l
  is-invertible-Monoid x =
    Σ ( type-Monoid M)
      ( λ y →
        Id (mul-Monoid M y x) (unit-Monoid M) ×
        Id (mul-Monoid M x y) (unit-Monoid M))
  
  all-elements-equal-is-invertible-Monoid :
    (x : type-Monoid M) → all-elements-equal (is-invertible-Monoid x)
  all-elements-equal-is-invertible-Monoid x
    (pair y (pair p q)) (pair y' (pair p' q')) =
    eq-subtype
      ( ( λ z →
        is-prop-prod
          ( is-set-type-Monoid M (mul-Monoid M z x) (unit-Monoid M))
          ( is-set-type-Monoid M (mul-Monoid M x z) (unit-Monoid M))))
      ( ( inv (left-unit-law-Monoid M y)) ∙
        ( ( inv (ap (λ z → mul-Monoid M z y) p')) ∙
          ( ( assoc-mul-Monoid M y' x y) ∙
            ( ( ap (mul-Monoid M y') q) ∙
              ( right-unit-law-Monoid M y')))))
  
  is-prop-is-invertible-Monoid :
    (x : type-Monoid M) → is-prop (is-invertible-Monoid x)
  is-prop-is-invertible-Monoid x =
    is-prop-all-elements-equal (all-elements-equal-is-invertible-Monoid x)

  has-right-inverse-Monoid : type-Monoid M → UU l
  has-right-inverse-Monoid x =
    Σ ( type-Monoid M)
      ( λ y → Id (mul-Monoid M x y) (unit-Monoid M))

  is-contr-has-right-inverse-Monoid :
    (x : type-Monoid M) → is-invertible-Monoid x →
    is-contr (has-right-inverse-Monoid x)
  pr1 (pr1 (is-contr-has-right-inverse-Monoid x (pair y (pair p q)))) = y
  pr2 (pr1 (is-contr-has-right-inverse-Monoid x (pair y (pair p q)))) = q
  pr2 (is-contr-has-right-inverse-Monoid x (pair y (pair p q))) (pair y' q') =
    eq-subtype
      ( λ u → is-set-type-Monoid M (mul-Monoid M x u) (unit-Monoid M))
      ( ( inv (right-unit-law-Monoid M y)) ∙
        ( ( ap (mul-Monoid M y) (inv q')) ∙
          ( ( inv (assoc-mul-Monoid M y x y')) ∙
            ( ( ap (mul-Monoid' M y') p) ∙
              ( left-unit-law-Monoid M y')))))

  has-left-inverse-Monoid : type-Monoid M → UU l
  has-left-inverse-Monoid x =
    Σ ( type-Monoid M)
      ( λ y → Id (mul-Monoid M y x) (unit-Monoid M))

  is-contr-has-left-inverse-Monoid :
    (x : type-Monoid M) → is-invertible-Monoid x →
    is-contr (has-left-inverse-Monoid x)
  pr1 (pr1 (is-contr-has-left-inverse-Monoid x (pair y (pair p q)))) = y
  pr2 (pr1 (is-contr-has-left-inverse-Monoid x (pair y (pair p q)))) = p
  pr2 (is-contr-has-left-inverse-Monoid x (pair y (pair p q))) (pair y' p') =
    eq-subtype
      ( λ u → is-set-type-Monoid M (mul-Monoid M u x) (unit-Monoid M))
      ( ( inv (left-unit-law-Monoid M y)) ∙
        ( ( ap (mul-Monoid' M y) (inv p')) ∙
          ( ( assoc-mul-Monoid M y' x y) ∙
            ( ( ap (mul-Monoid M y') q) ∙
              ( right-unit-law-Monoid M y')))))

--------------------------------------------------------------------------------

{- The property that a monoid is a group is just the property that the monoid
   that every element is invertible, i.e., it comes equipped with an inverse
   operation that satisfies the left and right inverse laws. -}

is-group' :
  {l : Level} (G : Semigroup l) → is-unital G → UU l
is-group' G is-unital-G =
  Σ ( type-Semigroup G → type-Semigroup G)
    ( λ i →
      ( (x : type-Semigroup G) →
        Id (mul-Semigroup G (i x) x) (pr1 is-unital-G)) ×
      ( (x : type-Semigroup G) →
        Id (mul-Semigroup G x (i x)) (pr1 is-unital-G)))

is-group :
  {l : Level} (G : Semigroup l) → UU l
is-group G =
  Σ (is-unital G) (is-group' G)

Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Semigroup l) is-group

{- Some bureaucracy of Groups. -}

module _
  {l : Level} (G : Group l)
  where
  
  semigroup-Group : Semigroup l
  semigroup-Group = pr1 G
  
  set-Group : UU-Set l
  set-Group = pr1 semigroup-Group
  
  type-Group : UU l
  type-Group = pr1 set-Group
  
  is-set-type-Group : is-set type-Group
  is-set-type-Group = pr2 set-Group
  
  associative-mul-Group : has-associative-mul type-Group
  associative-mul-Group = pr2 semigroup-Group
  
  mul-Group : type-Group → type-Group → type-Group
  mul-Group = pr1 associative-mul-Group

  ap-mul-Group :
    {x x' y y' : type-Group} (p : Id x x') (q : Id y y') →
    Id (mul-Group x y) (mul-Group x' y')
  ap-mul-Group p q = ap-binary mul-Group p q
  
  mul-Group' : type-Group → type-Group → type-Group
  mul-Group' x y = mul-Group y x
  
  assoc-mul-Group :
    (x y z : type-Group) →
    Id (mul-Group (mul-Group x y) z) (mul-Group x (mul-Group y z))
  assoc-mul-Group = pr2 associative-mul-Group
    
  is-group-Group : is-group semigroup-Group
  is-group-Group = pr2 G
  
  is-unital-Group : is-unital semigroup-Group
  is-unital-Group = pr1 is-group-Group

  monoid-Group : Monoid l
  pr1 monoid-Group = semigroup-Group
  pr2 monoid-Group = is-unital-Group
  
  unit-Group : type-Group
  unit-Group = pr1 is-unital-Group
  
  left-unit-law-Group :
    (x : type-Group) → Id (mul-Group unit-Group x) x
  left-unit-law-Group = pr1 (pr2 is-unital-Group)
  
  right-unit-law-Group :
    (x : type-Group) → Id (mul-Group x unit-Group) x
  right-unit-law-Group = pr2 (pr2 is-unital-Group)
  
  has-inverses-Group : is-group' semigroup-Group is-unital-Group
  has-inverses-Group = pr2 is-group-Group
  
  inv-Group : type-Group → type-Group
  inv-Group = pr1 has-inverses-Group
  
  left-inverse-law-Group :
    (x : type-Group) → Id (mul-Group (inv-Group x) x) unit-Group
  left-inverse-law-Group = pr1 (pr2 has-inverses-Group)
  
  right-inverse-law-Group :
    (x : type-Group) → Id (mul-Group x (inv-Group x)) unit-Group
  right-inverse-law-Group = pr2 (pr2 has-inverses-Group)

  is-equiv-mul-Group : (x : type-Group) → is-equiv (mul-Group x)
  is-equiv-mul-Group x =
    is-equiv-has-inverse
      ( mul-Group (inv-Group x))
      ( λ y →
        ( inv (assoc-mul-Group _ _ _)) ∙
        ( ( ap (mul-Group' y) (right-inverse-law-Group x)) ∙
          ( left-unit-law-Group y)))
      ( λ y →
        ( inv (assoc-mul-Group _ _ _)) ∙
        ( ( ap (mul-Group' y) (left-inverse-law-Group x)) ∙
          ( left-unit-law-Group y)))
  
  equiv-mul-Group : (x : type-Group) → type-Group ≃ type-Group
  pr1 (equiv-mul-Group x) = mul-Group x
  pr2 (equiv-mul-Group x) = is-equiv-mul-Group x
  
  is-equiv-mul-Group' : (x : type-Group) → is-equiv (mul-Group' x)
  is-equiv-mul-Group' x =
    is-equiv-has-inverse
    ( mul-Group' (inv-Group x))
      ( λ y →
        ( assoc-mul-Group _ _ _) ∙
        ( ( ap (mul-Group y) (left-inverse-law-Group x)) ∙
          ( right-unit-law-Group y)))
      ( λ y →
        ( assoc-mul-Group _ _ _) ∙
        ( ( ap (mul-Group y) (right-inverse-law-Group x)) ∙
          ( right-unit-law-Group y)))
  
  equiv-mul-Group' : (x : type-Group) → type-Group ≃ type-Group
  pr1 (equiv-mul-Group' x) = mul-Group' x
  pr2 (equiv-mul-Group' x) = is-equiv-mul-Group' x

  equiv-conjugation-Group : (x : type-Group) → type-Group ≃ type-Group
  equiv-conjugation-Group x =
    equiv-mul-Group' (inv-Group x) ∘e equiv-mul-Group x

  distributive-inv-mul-Group :
    (x y : type-Group) →
    Id (inv-Group (mul-Group x y)) (mul-Group (inv-Group y) (inv-Group x))
  distributive-inv-mul-Group x y =
    ap pr1
      ( eq-is-contr'
        ( is-contr-has-left-inverse-Monoid monoid-Group
          ( mul-Group x y)
          ( pair
            ( inv-Group (mul-Group x y))
            ( pair
              ( left-inverse-law-Group (mul-Group x y))
              ( right-inverse-law-Group (mul-Group x y)))))
        ( pair
            ( inv-Group (mul-Group x y))
            ( left-inverse-law-Group (mul-Group x y)))
        ( pair
            ( mul-Group (inv-Group y) (inv-Group x))
            ( ( assoc-mul-Group
                ( inv-Group y)
                ( inv-Group x)
                ( mul-Group x y)) ∙
              ( ( ap
                  ( mul-Group (inv-Group y))
                  ( ( inv (assoc-mul-Group (inv-Group x) x y)) ∙
                    ( ( ap (mul-Group' y) (left-inverse-law-Group x)) ∙
                      ( left-unit-law-Group y)))) ∙
                ( left-inverse-law-Group y)))))

  conjugation-Group : (x : type-Group) → type-Group → type-Group
  conjugation-Group x = map-equiv (equiv-conjugation-Group x)

  {- We show that being a group is a proposition. -}
  
abstract
  all-elements-equal-is-group :
    {l : Level} (G : Semigroup l) (e : is-unital G) →
    all-elements-equal (is-group' G e)
  all-elements-equal-is-group
    ( pair (pair G is-set-G) (pair μ assoc-G))
    ( pair e (pair left-unit-G right-unit-G))
    ( pair i (pair left-inv-i right-inv-i))
    ( pair i' (pair left-inv-i' right-inv-i')) =
    eq-subtype
      ( λ i →
        is-prop-prod
          ( is-prop-Π (λ x → is-set-G (μ (i x) x) e))
          ( is-prop-Π (λ x → is-set-G (μ x (i x)) e)))
      ( eq-htpy
        ( λ x →                                             -- ix
          ( inv (left-unit-G (i x))) ∙                      -- = 1·(ix)
          ( ( ap (λ y → μ y (i x)) (inv (left-inv-i' x))) ∙ -- = (i'x·x)·(ix)
            ( ( assoc-G (i' x) x (i x)) ∙                   -- = (i'x)·(x·ix)
              ( ( ap (μ (i' x)) (right-inv-i x)) ∙          -- = (i'x)·1
                ( right-unit-G (i' x)))))))                 -- = i'x

abstract
  is-prop-is-group :
    {l : Level} (G : Semigroup l) → is-prop (is-group G)
  is-prop-is-group G =
    is-prop-Σ
      ( is-prop-is-unital G)
      ( λ e →
        is-prop-all-elements-equal (all-elements-equal-is-group G e))

is-group-Prop : {l : Level} (G : Semigroup l) → UU-Prop l
pr1 (is-group-Prop G) = is-group G
pr2 (is-group-Prop G) = is-prop-is-group G

{- We introduce group homomorphisms. -}

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-mul-Group : (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-mul-Group f =
    preserves-mul-Semigroup (semigroup-Group G) (semigroup-Group H) f

  type-hom-Group : UU (l1 ⊔ l2)
  type-hom-Group =
    type-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  {- Bureaucracy of group homomorphisms. -}
  
  map-hom-Group : type-hom-Group → type-Group G → type-Group H
  map-hom-Group = pr1

  preserves-mul-hom-Group :
    (f : type-hom-Group) →
    preserves-mul-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( map-hom-Group f)
  preserves-mul-hom-Group = pr2

  emb-Group : UU (l1 ⊔ l2)
  emb-Group = Σ type-hom-Group (λ h → is-emb (map-hom-Group h))

  {- We characterize the identity type of the group homomorphisms. -}

  htpy-hom-Group : (f g : type-hom-Group) → UU (l1 ⊔ l2)
  htpy-hom-Group = htpy-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  refl-htpy-hom-Group : (f : type-hom-Group) → htpy-hom-Group f f
  refl-htpy-hom-Group =
    refl-htpy-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  htpy-eq-hom-Group : (f g : type-hom-Group) → Id f g → htpy-hom-Group f g
  htpy-eq-hom-Group =
    htpy-eq-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  abstract
    is-contr-total-htpy-hom-Group :
      ( f : type-hom-Group) →
      is-contr (Σ type-hom-Group (htpy-hom-Group f))
    is-contr-total-htpy-hom-Group =
      is-contr-total-htpy-hom-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)

  abstract
    is-equiv-htpy-eq-hom-Group :
      (f g : type-hom-Group) → is-equiv (htpy-eq-hom-Group f g)
    is-equiv-htpy-eq-hom-Group =
      is-equiv-htpy-eq-hom-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)

  extensionality-hom-Group : (f g : type-hom-Group) → Id f g ≃ htpy-hom-Group f g
  pr1 (extensionality-hom-Group f g) = htpy-eq-hom-Group f g
  pr2 (extensionality-hom-Group f g) = is-equiv-htpy-eq-hom-Group f g

  eq-htpy-hom-Group : {f g : type-hom-Group} → htpy-hom-Group f g → Id f g
  eq-htpy-hom-Group =
    eq-htpy-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-set-type-hom-Group : is-set type-hom-Group
  is-set-type-hom-Group =
    is-set-type-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-Group : UU-Set (l1 ⊔ l2)
  pr1 hom-Group = type-hom-Group
  pr2 hom-Group = is-set-type-hom-Group

{- We define the precategory of groups -}

id-hom-Group : {l : Level} (G : Group l) → type-hom-Group G G
id-hom-Group G = id-hom-Semigroup (semigroup-Group G)

comp-hom-Group :
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3) →
  type-hom-Group H K → type-hom-Group G H → type-hom-Group G K
comp-hom-Group G H K =
  comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)
    ( semigroup-Group K)

associative-comp-hom-Group :
  {l1 l2 l3 l4 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3) (L : Group l4)
  (h : type-hom-Group K L) (g : type-hom-Group H K) (f : type-hom-Group G H) →
  Id ( comp-hom-Group G H L (comp-hom-Group H K L h g) f)
     ( comp-hom-Group G K L h (comp-hom-Group G H K g f))
associative-comp-hom-Group G H K L =
  associative-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)
    ( semigroup-Group K)
    ( semigroup-Group L)

left-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H) →
  Id (comp-hom-Group G H H (id-hom-Group H) f) f
left-unit-law-comp-hom-Group G H =
  left-unit-law-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)

right-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H) →
  Id (comp-hom-Group G G H f (id-hom-Group G)) f
right-unit-law-comp-hom-Group G H =
  right-unit-law-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)

Group-Large-Precat : Large-Precat
obj-Large-Precat Group-Large-Precat = Group
hom-Large-Precat Group-Large-Precat = hom-Group
comp-hom-Large-Precat Group-Large-Precat = comp-hom-Group
id-hom-Large-Precat Group-Large-Precat = id-hom-Group
associative-comp-hom-Large-Precat Group-Large-Precat =
  associative-comp-hom-Group
left-unit-law-comp-hom-Large-Precat Group-Large-Precat =
  left-unit-law-comp-hom-Group
right-unit-law-comp-hom-Large-Precat Group-Large-Precat =
  right-unit-law-comp-hom-Group

Group-Precat : (l : Level) → Precat (lsuc l) l
pr1 (Group-Precat l) = Group l
pr1 (pr2 (Group-Precat l)) = hom-Group
pr1 (pr1 (pr2 (pr2 (Group-Precat l)))) {G} {H} {K} = comp-hom-Group G H K
pr2 (pr1 (pr2 (pr2 (Group-Precat l)))) {G} {H} {K} {L} = associative-comp-hom-Group G H K L
pr1 (pr2 (pr2 (pr2 (Group-Precat l)))) = id-hom-Group
pr1 (pr2 (pr2 (pr2 (pr2 (Group-Precat l))))) {G} {H} = left-unit-law-comp-hom-Group G H
pr2 (pr2 (pr2 (pr2 (pr2 (Group-Precat l))))) {G} {H} = right-unit-law-comp-hom-Group G H

{- We show that the precategory of groups is a category -}

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where
  
  is-iso-hom-Group : type-hom-Group G H → UU (l1 ⊔ l2)
  is-iso-hom-Group = is-iso-hom-Large-Precat Group-Large-Precat G H

  type-iso-Group : UU (l1 ⊔ l2)
  type-iso-Group = type-iso-Large-Precat Group-Large-Precat G H

  hom-iso-Group : type-iso-Group → type-hom-Group G H
  hom-iso-Group = hom-iso-Large-Precat Group-Large-Precat G H

  is-iso-hom-iso-Group :
    (f : type-iso-Group) → is-iso-hom-Group (hom-iso-Group f)
  is-iso-hom-iso-Group = is-iso-hom-iso-Large-Precat Group-Large-Precat G H

  hom-inv-iso-Group : type-iso-Group → type-hom-Group H G
  hom-inv-iso-Group = hom-inv-iso-Large-Precat Group-Large-Precat G H

  equiv-Group : UU (l1 ⊔ l2)
  equiv-Group = equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  equiv-iso-equiv-Group : equiv-Group ≃ type-iso-Group
  equiv-iso-equiv-Group =
    equiv-iso-equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  iso-equiv-Group : equiv-Group → type-iso-Group
  iso-equiv-Group = map-equiv equiv-iso-equiv-Group

module _
  {l : Level} (G : Group l)
  where

  id-iso-Group : type-iso-Group G G
  id-iso-Group = id-iso-Large-Precat Group-Large-Precat G

  iso-eq-Group : (H : Group l) → Id G H → type-iso-Group G H
  iso-eq-Group = iso-eq-Large-Precat Group-Large-Precat G

  abstract
    extensionality-Group' : (H : Group l) → Id G H ≃ type-iso-Group G H
    extensionality-Group' H =
      ( extensionality-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)) ∘e
      ( equiv-ap-pr1 is-prop-is-group {s = G} {t = H})

  abstract
    is-contr-total-iso-Group : is-contr (Σ (Group l) (type-iso-Group G))
    is-contr-total-iso-Group =
      is-contr-equiv'
        ( Σ (Group l) (Id G))
        ( equiv-tot extensionality-Group')
        ( is-contr-total-path G)

is-category-Group : is-category-Large-Precat Group-Large-Precat
is-category-Group G =
  fundamental-theorem-id G
    ( id-iso-Group G)
    ( is-contr-total-iso-Group G)
    ( iso-eq-Group G)

eq-iso-Group : {l : Level} (G H : Group l) → type-iso-Group G H → Id G H
eq-iso-Group G H = map-inv-is-equiv (is-category-Group G H)

Group-Large-Cat : Large-Cat
precat-Large-Cat Group-Large-Cat = Group-Large-Precat
is-category-Large-Cat Group-Large-Cat = is-category-Group
```
### Examples of groups

#### The group of integers

```agda
ℤ-Semigroup : Semigroup lzero
pr1 ℤ-Semigroup = ℤ-Set
pr1 (pr2 ℤ-Semigroup) = add-ℤ
pr2 (pr2 ℤ-Semigroup) = associative-add-ℤ

ℤ-Group : Group lzero
pr1 ℤ-Group = ℤ-Semigroup
pr1 (pr1 (pr2 ℤ-Group)) = zero-ℤ
pr1 (pr2 (pr1 (pr2 ℤ-Group))) = left-unit-law-add-ℤ
pr2 (pr2 (pr1 (pr2 ℤ-Group))) = right-unit-law-add-ℤ
pr1 (pr2 (pr2 ℤ-Group)) = neg-ℤ
pr1 (pr2 (pr2 (pr2 ℤ-Group))) = left-inverse-law-add-ℤ
pr2 (pr2 (pr2 (pr2 ℤ-Group))) = right-inverse-law-add-ℤ
```

#### The group of integers modulo k

```agda
ℤ-Mod-Semigroup : (k : ℕ) → Semigroup lzero
pr1 (ℤ-Mod-Semigroup k) = ℤ-Mod-Set k
pr1 (pr2 (ℤ-Mod-Semigroup k)) = add-ℤ-Mod k
pr2 (pr2 (ℤ-Mod-Semigroup k)) = associative-add-ℤ-Mod k

ℤ-Mod-Group : (k : ℕ) → Group lzero
pr1 (ℤ-Mod-Group k) = ℤ-Mod-Semigroup k
pr1 (pr1 (pr2 (ℤ-Mod-Group k))) = zero-ℤ-Mod k
pr1 (pr2 (pr1 (pr2 (ℤ-Mod-Group k)))) = left-unit-law-add-ℤ-Mod k
pr2 (pr2 (pr1 (pr2 (ℤ-Mod-Group k)))) = right-unit-law-add-ℤ-Mod k
pr1 (pr2 (pr2 (ℤ-Mod-Group k))) = neg-ℤ-Mod k
pr1 (pr2 (pr2 (pr2 (ℤ-Mod-Group k)))) = left-inverse-law-add-ℤ-Mod k
pr2 (pr2 (pr2 (pr2 (ℤ-Mod-Group k)))) = right-inverse-law-add-ℤ-Mod k
```

#### The group of loops in a 1-type

```agda
loop-space :
  {l : Level} {A : UU l} → A → UU l
loop-space a = Id a a

loop-space-Set :
  {l : Level} (A : UU l) (a : A) (is-set-Ω : is-set (Id a a)) → UU-Set l
pr1 (loop-space-Set A a is-set-Ω) = Id a a
pr2 (loop-space-Set A a is-set-Ω) = is-set-Ω

loop-space-Semigroup :
  {l : Level} (A : UU l) (a : A) (is-set-Ω : is-set (Id a a)) → Semigroup l
pr1 (loop-space-Semigroup A a is-set-Ω) = loop-space-Set A a is-set-Ω
pr1 (pr2 (loop-space-Semigroup A a is-set-Ω)) p q = p ∙ q
pr2 (pr2 (loop-space-Semigroup A a is-set-Ω)) = assoc

loop-space-Group :
  {l : Level} (A : UU l) (a : A) (is-set-Ω : is-set (Id a a)) → Group l
pr1 (loop-space-Group A a is-set-Ω) = loop-space-Semigroup A a is-set-Ω
pr1 (pr1 (pr2 (loop-space-Group A a is-set-Ω))) = refl
pr1 (pr2 (pr1 (pr2 (loop-space-Group A a is-set-Ω)))) q = left-unit
pr2 (pr2 (pr1 (pr2 (loop-space-Group A a is-set-Ω)))) p = right-unit
pr1 (pr2 (pr2 (loop-space-Group A a is-set-Ω))) = inv
pr1 (pr2 (pr2 (pr2 (loop-space-Group A a is-set-Ω)))) = left-inv
pr2 (pr2 (pr2 (pr2 (loop-space-Group A a is-set-Ω)))) = right-inv

loop-space-1-type-Set :
  {l : Level} (A : UU-1-Type l) (a : type-1-Type A) → UU-Set l
loop-space-1-type-Set A a =
  loop-space-Set (type-1-Type A) a (is-1-type-type-1-Type A a a)

loop-space-1-type-Semigroup :
  {l : Level} (A : UU-1-Type l) (a : type-1-Type A) → Semigroup l
loop-space-1-type-Semigroup A a =
  loop-space-Semigroup (type-1-Type A) a (is-1-type-type-1-Type A a a)

loop-space-1-type-Group :
  {l : Level} (A : UU-1-Type l) (a : type-1-Type A) → Group l
loop-space-1-type-Group A a =
  loop-space-Group (type-1-Type A) a (is-1-type-type-1-Type A a a)
```

#### The symmetric group on a set

```agda
set-symmetric-Group : {l : Level} (X : UU-Set l) → UU-Set l
set-symmetric-Group X = aut-Set X

type-symmetric-Group : {l : Level} (X : UU-Set l) → UU l
type-symmetric-Group X = type-Set (set-symmetric-Group X)

is-set-type-symmetric-Group :
  {l : Level} (X : UU-Set l) → is-set (type-symmetric-Group X)
is-set-type-symmetric-Group X = is-set-type-Set (set-symmetric-Group X)

has-associative-mul-aut-Set :
  {l : Level} (X : UU-Set l) → has-associative-mul-Set (aut-Set X)
pr1 (has-associative-mul-aut-Set X) f e = f ∘e e
pr2 (has-associative-mul-aut-Set X) e f g = associative-comp-equiv g f e

symmetric-Semigroup :
  {l : Level} (X : UU-Set l) → Semigroup l
pr1 (symmetric-Semigroup X) = set-symmetric-Group X
pr2 (symmetric-Semigroup X) = has-associative-mul-aut-Set X

is-unital-symmetric-Semigroup :
  {l : Level} (X : UU-Set l) → is-unital (symmetric-Semigroup X)
pr1 (is-unital-symmetric-Semigroup X) = id-equiv
pr1 (pr2 (is-unital-symmetric-Semigroup X)) = left-unit-law-equiv
pr2 (pr2 (is-unital-symmetric-Semigroup X)) = right-unit-law-equiv

is-group-symmetric-Semigroup' :
  {l : Level} (X : UU-Set l) →
  is-group' (symmetric-Semigroup X) (is-unital-symmetric-Semigroup X)
pr1 (is-group-symmetric-Semigroup' X) = inv-equiv
pr1 (pr2 (is-group-symmetric-Semigroup' X)) = left-inverse-law-equiv
pr2 (pr2 (is-group-symmetric-Semigroup' X)) = right-inverse-law-equiv

symmetric-Group :
  {l : Level} → UU-Set l → Group l
pr1 (symmetric-Group X) = symmetric-Semigroup X
pr1 (pr2 (symmetric-Group X)) = is-unital-symmetric-Semigroup X
pr2 (pr2 (symmetric-Group X)) = is-group-symmetric-Semigroup' X

--------------------------------------------------------------------------------

-- Exercises

--------------------------------------------------------------------------------

-- Exercise

{- We show that group homomorphisms preserve the unit. -}

preserves-unit :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : type-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)) →
  UU l2
preserves-unit G H f =
  Id (map-hom-Group G H f (unit-Group G)) (unit-Group H)

abstract
  preserves-unit-hom-Group :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : type-hom-Group G H) → preserves-unit G H f
  preserves-unit-hom-Group G H f =
    ( inv (left-unit-law-Group H (map-hom-Group G H f (unit-Group G)))) ∙
    ( ( ap ( λ x → mul-Group H x (map-hom-Group G H f (unit-Group G)))
           ( inv
             ( left-inverse-law-Group H
               ( map-hom-Group G H f (unit-Group G))))) ∙
      ( ( assoc-mul-Group H
          ( inv-Group H (map-hom-Group G H f (unit-Group G)))
          ( map-hom-Group G H f (unit-Group G))
          ( map-hom-Group G H f (unit-Group G))) ∙
        ( ( ap
            ( mul-Group H (inv-Group H (map-hom-Group G H f (unit-Group G))))
            ( inv
              ( preserves-mul-hom-Group G H f (unit-Group G) (unit-Group G)))) ∙
          ( ( ap
              ( λ x →
                mul-Group H
                  ( inv-Group H (map-hom-Group G H f (unit-Group G)))
                  ( map-hom-Group G H f x))
              ( left-unit-law-Group G (unit-Group G))) ∙
            ( left-inverse-law-Group H (map-hom-Group G H f (unit-Group G)))))))

{- We show that group homomorphisms preserve inverses. -}

preserves-inverses :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : type-hom-Group G H) → UU (l1 ⊔ l2)
preserves-inverses G H f =
  ( x : type-Group G) →
  Id ( map-hom-Group G H f (inv-Group G x))
     ( inv-Group H (map-hom-Group G H f x))

abstract
  preserves-inverses-hom-Group' :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : type-hom-Group G H) →
    preserves-unit G H f → preserves-inverses G H f
  preserves-inverses-hom-Group'
    ( pair ( pair (pair G is-set-G) (pair μ-G assoc-G))
           ( pair ( pair e-G (pair left-unit-G right-unit-G))
                  ( pair i-G (pair left-inv-G right-inv-G))))
    ( pair ( pair (pair H is-set-H) (pair μ-H assoc-H))
           ( pair ( pair e-H (pair left-unit-H right-unit-H))
                  ( pair i-H (pair left-inv-H right-inv-H))))
    ( pair f μ-f) preserves-unit-f x =
    ( inv ( right-unit-H (f (i-G x)))) ∙
    ( ( ap (μ-H (f (i-G x))) (inv (right-inv-H (f x)))) ∙
      ( ( inv (assoc-H (f (i-G x)) (f x) (i-H (f x)))) ∙
        ( ( inv (ap (λ y → μ-H y (i-H (f x))) (μ-f (i-G x) x))) ∙
          ( ( ap (λ y → μ-H (f y) (i-H (f x))) (left-inv-G x)) ∙
            ( ( ap
                ( λ y → μ-H y (i-H (f x)))
                ( preserves-unit-f)) ∙
              ( left-unit-H (i-H (f x))))))))

abstract
  preserves-inverses-hom-Group :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : type-hom-Group G H) → preserves-inverses G H f
  preserves-inverses-hom-Group G H f =
    preserves-inverses-hom-Group' G H f (preserves-unit-hom-Group G H f)

hom-Group' :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
hom-Group' G H =
  Σ ( type-hom-Group G H) (λ f →
    ( preserves-unit G H f) × (preserves-inverses G H f))

preserves-group-structure-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  type-hom-Group G H → hom-Group' G H
pr1 (preserves-group-structure-hom-Group G H f) = f
pr1 (pr2 (preserves-group-structure-hom-Group G H f)) =
  preserves-unit-hom-Group G H f
pr2 (pr2 (preserves-group-structure-hom-Group G H f)) =
  preserves-inverses-hom-Group G H f

--------------------------------------------------------------------------------

-- Cayley's Theorem

module _
  {l1 : Level} (G : Group l1)
  where
  
  map-Cayleys-theorem :
    type-Group G → type-Group (symmetric-Group (set-Group G))
  map-Cayleys-theorem x = equiv-mul-Group G x
  
  preserves-mul-map-Cayleys-theorem :
    preserves-mul-Group G (symmetric-Group (set-Group G)) map-Cayleys-theorem
  preserves-mul-map-Cayleys-theorem x y =
    eq-htpy-equiv (λ z → assoc-mul-Group G x y z)

  hom-Cayleys-theorem : type-hom-Group G (symmetric-Group (set-Group G))
  hom-Cayleys-theorem =
    pair map-Cayleys-theorem preserves-mul-map-Cayleys-theorem

  is-injective-map-Cayleys-theorem : is-injective map-Cayleys-theorem
  is-injective-map-Cayleys-theorem {x} {y} p =
    ( inv (right-unit-law-Group G x)) ∙
    ( ( htpy-eq-equiv p (unit-Group G)) ∙
      ( right-unit-law-Group G y))

  is-emb-map-Cayleys-theorem : is-emb map-Cayleys-theorem
  is-emb-map-Cayleys-theorem =
    is-emb-is-injective
      ( is-set-type-Group (symmetric-Group (set-Group G)))
      ( is-injective-map-Cayleys-theorem)

  Cayleys-theorem : emb-Group G (symmetric-Group (set-Group G))
  Cayleys-theorem = pair hom-Cayleys-theorem is-emb-map-Cayleys-theorem
```
