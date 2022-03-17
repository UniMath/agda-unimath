# Homomorphisms of groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.homomorphisms-groups where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.identity-types using (Id; inv; _∙_; ap)
open import foundation.sets using (is-set; UU-Set)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.groups using
  ( Group; type-Group; semigroup-Group; unit-Group; left-unit-law-Group;
    mul-Group; left-inverse-law-Group; assoc-mul-Group; inv-Group)
open import group-theory.homomorphisms-semigroups using
  ( preserves-mul-Semigroup; type-hom-Semigroup; htpy-hom-Semigroup;
    refl-htpy-hom-Semigroup; htpy-eq-hom-Semigroup;
    is-contr-total-htpy-hom-Semigroup; is-equiv-htpy-eq-hom-Semigroup;
    eq-htpy-hom-Semigroup; is-set-type-hom-Semigroup; id-hom-Semigroup;
    comp-hom-Semigroup; associative-comp-hom-Semigroup;
    left-unit-law-comp-hom-Semigroup; right-unit-law-comp-hom-Semigroup)
```

## Idea

A group homomorphism from one group to another is a semigroup homomorphism between their underlying semigroups

## Definition

```agda
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
```

## Properties

```agda
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
```
