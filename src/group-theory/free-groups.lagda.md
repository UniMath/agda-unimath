# Free groups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.free-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.binary-relations
open import foundation.sets
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sections
open import foundation.retractions
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.unital-binary-operations
open import group-theory.semigroups
open import foundation.equivalences
open import group-theory.monoids
open import foundation.homotopies
open import group-theory.homomorphisms-groups
open import group-theory.groups
open import foundation.action-on-identifications-binary-functions
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.functoriality-propositional-truncation
open import foundation.set-quotients
open import foundation.dependent-pair-types
open import foundation.truncation-equivalence-relations
open import foundation.binary-functoriality-set-quotients
open import foundation.functoriality-set-quotients
open import foundation.equivalence-relations
```

</details>

## Idea

## Definition

```agda
data word-free-Group {l : Level} (A : UU l) : UU l where
  in-generator-word-free-Group : A → word-free-Group A
  inv-word-free-Group : word-free-Group A → word-free-Group A
  mul-word-free-Group :
    word-free-Group A → word-free-Group A → word-free-Group A
  unit-word-free-Group : word-free-Group A

data
  equiv-word-free-Group {l : Level} (A : UU l) :
    Relation l (word-free-Group A)
  where

  refl-equiv-word-free-Group :
    (w : word-free-Group A) → equiv-word-free-Group A w w
  symmetric-equiv-word-free-Group :
    (x y : word-free-Group A) →
    equiv-word-free-Group A x y →
    equiv-word-free-Group A y x
  transitive-equiv-word-free-Group :
    (x y z : word-free-Group A) →
    equiv-word-free-Group A y z →
    equiv-word-free-Group A x y →
    equiv-word-free-Group A x z

  ap-mul-word-free-Group :
    (x x' y y' : word-free-Group A) →
    equiv-word-free-Group A x x' → equiv-word-free-Group A y y' →
    equiv-word-free-Group A
      ( mul-word-free-Group x y)
      ( mul-word-free-Group x' y')
  ap-inv-word-free-Group :
    (x x' : word-free-Group A) → equiv-word-free-Group A x x' →
    equiv-word-free-Group A
      ( inv-word-free-Group x)
      ( inv-word-free-Group x')

  associative-mul-equiv-word-free-Group :
    (x y z : word-free-Group A) →
    equiv-word-free-Group A
      ( mul-word-free-Group (mul-word-free-Group x y) z)
      ( mul-word-free-Group x (mul-word-free-Group y z))

  left-unit-law-equiv-word-free-Group :
    (x : word-free-Group A) →
    equiv-word-free-Group A (mul-word-free-Group unit-word-free-Group x) x
  right-unit-law-equiv-word-free-Group :
    (x : word-free-Group A) →
    equiv-word-free-Group A (mul-word-free-Group x unit-word-free-Group) x

  left-inverse-law-equiv-word-free-Group :
    (x : word-free-Group A) →
    equiv-word-free-Group A
      ( mul-word-free-Group (inv-word-free-Group x) x)
      ( unit-word-free-Group)
  right-inverse-law-equiv-word-free-Group :
    (x : word-free-Group A) →
    equiv-word-free-Group A
      ( mul-word-free-Group x (inv-word-free-Group x))
      ( unit-word-free-Group)

equivalence-relation-word-free-Group :
  {l : Level} (A : UU l) → equivalence-relation l (word-free-Group A)
equivalence-relation-word-free-Group A =
  equivalence-relation-trunc-Relation
    ( equiv-word-free-Group A)
    ( refl-equiv-word-free-Group)
    ( symmetric-equiv-word-free-Group)
    ( transitive-equiv-word-free-Group)

module _
  {l : Level}
  (A : UU l)
  where

  set-free-Group : Set l
  set-free-Group = quotient-Set (equivalence-relation-word-free-Group A)

  type-free-Group : UU l
  type-free-Group = type-Set set-free-Group

  in-word-free-Group : word-free-Group A → type-free-Group
  in-word-free-Group =
    quotient-map
      ( equivalence-relation-word-free-Group A)

  in-free-Group : A → type-free-Group
  in-free-Group a =
    in-word-free-Group (in-generator-word-free-Group a)

  abstract
    in-equiv-word-free-Group :
      {x y : word-free-Group A} →
      equiv-word-free-Group A x y →
      in-word-free-Group x ＝ in-word-free-Group y
    in-equiv-word-free-Group H =
      apply-effectiveness-quotient-map'
        ( equivalence-relation-word-free-Group A)
        ( unit-trunc-Prop H)

  binary-hom-mul-free-Group :
    binary-hom-equivalence-relation
      ( equivalence-relation-word-free-Group A)
      ( equivalence-relation-word-free-Group A)
      ( equivalence-relation-word-free-Group A)
  binary-hom-mul-free-Group =
    ( mul-word-free-Group ,
      map-binary-trunc-Prop (ap-mul-word-free-Group _ _ _ _))

  mul-free-Group : type-free-Group → type-free-Group → type-free-Group
  mul-free-Group =
    binary-map-set-quotient
      ( equivalence-relation-word-free-Group A)
      ( equivalence-relation-word-free-Group A)
      ( equivalence-relation-word-free-Group A)
      ( binary-hom-mul-free-Group)

  hom-inv-free-Group :
    hom-equivalence-relation
      ( equivalence-relation-word-free-Group A)
      ( equivalence-relation-word-free-Group A)
  hom-inv-free-Group =
    ( inv-word-free-Group ,
      map-trunc-Prop (ap-inv-word-free-Group _ _))

  inv-free-Group : type-free-Group → type-free-Group
  inv-free-Group =
    map-set-quotient
      ( equivalence-relation-word-free-Group A)
      ( equivalence-relation-word-free-Group A)
      ( hom-inv-free-Group)

  unit-free-Group : type-free-Group
  unit-free-Group = in-word-free-Group unit-word-free-Group

  abstract
    compute-mul-free-Group :
      (x y : word-free-Group A) →
      mul-free-Group (in-word-free-Group x) (in-word-free-Group y) ＝
      in-word-free-Group (mul-word-free-Group x y)
    compute-mul-free-Group =
      compute-binary-map-set-quotient
        ( equivalence-relation-word-free-Group A)
        ( equivalence-relation-word-free-Group A)
        ( equivalence-relation-word-free-Group A)
        ( binary-hom-mul-free-Group)

    compute-inv-free-Group :
      (x : word-free-Group A) →
      inv-free-Group (in-word-free-Group x) ＝
      in-word-free-Group (inv-word-free-Group x)
    compute-inv-free-Group =
      coherence-square-map-set-quotient
        ( equivalence-relation-word-free-Group A)
        ( equivalence-relation-word-free-Group A)
        ( hom-inv-free-Group)

    associative-mul-free-Group :
      (x y z : type-free-Group) →
      mul-free-Group (mul-free-Group x y) z ＝
      mul-free-Group x (mul-free-Group y z)
    associative-mul-free-Group =
      triple-induction-set-quotient'
        ( equivalence-relation-word-free-Group A)
        ( λ x y z →
          Id-Prop
            ( set-free-Group)
            ( mul-free-Group (mul-free-Group x y) z)
            ( mul-free-Group x (mul-free-Group y z)))
        ( λ x y z →
          ( ap-binary mul-free-Group (compute-mul-free-Group x y) refl) ∙
          ( compute-mul-free-Group _ _) ∙
          ( in-equiv-word-free-Group
            ( associative-mul-equiv-word-free-Group x y z)) ∙
          ( inv (compute-mul-free-Group _ _)) ∙
          ( ap-binary mul-free-Group refl (inv (compute-mul-free-Group y z))))

    left-unit-law-mul-free-Group :
      (x : type-free-Group) → mul-free-Group unit-free-Group x ＝ x
    left-unit-law-mul-free-Group =
      induction-set-quotient
        ( equivalence-relation-word-free-Group A)
        ( λ x →
          Id-Prop
            ( set-free-Group)
            ( mul-free-Group unit-free-Group x)
            ( x))
        ( λ x →
          ( compute-mul-free-Group _ _) ∙
          ( in-equiv-word-free-Group (left-unit-law-equiv-word-free-Group x)))

    right-unit-law-mul-free-Group :
      (x : type-free-Group) → mul-free-Group x unit-free-Group ＝ x
    right-unit-law-mul-free-Group =
      induction-set-quotient
        ( equivalence-relation-word-free-Group A)
        ( λ x →
          Id-Prop
            ( set-free-Group)
            ( mul-free-Group x unit-free-Group)
            ( x))
        ( λ x →
          ( compute-mul-free-Group _ _) ∙
          ( in-equiv-word-free-Group (right-unit-law-equiv-word-free-Group x)))

    left-inverse-law-mul-free-Group :
      (x : type-free-Group) →
      mul-free-Group (inv-free-Group x) x ＝ unit-free-Group
    left-inverse-law-mul-free-Group =
      induction-set-quotient
        ( equivalence-relation-word-free-Group A)
        ( λ x →
          Id-Prop
            ( set-free-Group)
            ( mul-free-Group (inv-free-Group x) x)
            ( unit-free-Group))
        ( λ x →
          ( ap-binary mul-free-Group (compute-inv-free-Group x) refl) ∙
          ( compute-mul-free-Group _ _) ∙
          ( in-equiv-word-free-Group
            ( left-inverse-law-equiv-word-free-Group x)))

    right-inverse-law-mul-free-Group :
      (x : type-free-Group) →
      mul-free-Group x (inv-free-Group x) ＝ unit-free-Group
    right-inverse-law-mul-free-Group =
      induction-set-quotient
        ( equivalence-relation-word-free-Group A)
        ( λ x →
          Id-Prop
            ( set-free-Group)
            ( mul-free-Group x (inv-free-Group x))
            ( unit-free-Group))
        ( λ x →
          ( ap-binary mul-free-Group refl (compute-inv-free-Group x)) ∙
          ( compute-mul-free-Group _ _) ∙
          ( in-equiv-word-free-Group
            ( right-inverse-law-equiv-word-free-Group x)))

  semigroup-free-Group : Semigroup l
  semigroup-free-Group =
    ( set-free-Group ,
      mul-free-Group ,
      associative-mul-free-Group)

  is-unital-mul-free-Group : is-unital mul-free-Group
  is-unital-mul-free-Group =
    ( unit-free-Group ,
      left-unit-law-mul-free-Group ,
      right-unit-law-mul-free-Group)

  monoid-free-Group : Monoid l
  monoid-free-Group =
    ( semigroup-free-Group ,
      is-unital-mul-free-Group)

  free-Group : Group l
  free-Group =
    ( semigroup-free-Group ,
      is-unital-mul-free-Group ,
      inv-free-Group ,
      left-inverse-law-mul-free-Group ,
      right-inverse-law-mul-free-Group)
```

## Properties

### The universal property of a free group

#### Any map from `A` to a group `G` induces a group homomorphism from the free group on `A` to `G`

```agda
module _
  {l1 l2 : Level}
  (A : UU l1)
  (G : Group l2)
  (f : A → type-Group G)
  where

  map-word-hom-universal-property-free-Group :
    word-free-Group A → type-Group G
  map-word-hom-universal-property-free-Group (in-generator-word-free-Group a) =
    f a
  map-word-hom-universal-property-free-Group (inv-word-free-Group x) =
    inv-Group G (map-word-hom-universal-property-free-Group x)
  map-word-hom-universal-property-free-Group unit-word-free-Group =
    unit-Group G
  map-word-hom-universal-property-free-Group (mul-word-free-Group x y) =
    mul-Group G
      ( map-word-hom-universal-property-free-Group x)
      ( map-word-hom-universal-property-free-Group y)

  abstract
    equiv-map-word-hom-universal-property-free-Group :
      (x y : word-free-Group A) →
      equiv-word-free-Group A x y →
      map-word-hom-universal-property-free-Group x ＝
      map-word-hom-universal-property-free-Group y
    equiv-map-word-hom-universal-property-free-Group
      x .x (refl-equiv-word-free-Group .x) =
      refl
    equiv-map-word-hom-universal-property-free-Group
      x y (symmetric-equiv-word-free-Group .y .x y~x) =
      inv (equiv-map-word-hom-universal-property-free-Group y x y~x)
    equiv-map-word-hom-universal-property-free-Group
      x y (transitive-equiv-word-free-Group .x z .y z~y x~z) =
      equiv-map-word-hom-universal-property-free-Group x z x~z ∙
      equiv-map-word-hom-universal-property-free-Group z y z~y
    equiv-map-word-hom-universal-property-free-Group
      (mul-word-free-Group (mul-word-free-Group x y) z)
      (mul-word-free-Group .x (mul-word-free-Group .y .z))
      (associative-mul-equiv-word-free-Group x y z) =
      associative-mul-Group G _ _ _
    equiv-map-word-hom-universal-property-free-Group
      (mul-word-free-Group x y) (mul-word-free-Group x' y')
      (ap-mul-word-free-Group .x .x' .y .y' x~x' y~y') =
      ap-mul-Group G
        ( equiv-map-word-hom-universal-property-free-Group x x' x~x')
        ( equiv-map-word-hom-universal-property-free-Group y y' y~y')
    equiv-map-word-hom-universal-property-free-Group
      (inv-word-free-Group x) (inv-word-free-Group y)
      (ap-inv-word-free-Group .x .y x~y) =
      ap
        ( inv-Group G)
        ( equiv-map-word-hom-universal-property-free-Group x y x~y)
    equiv-map-word-hom-universal-property-free-Group
      (mul-word-free-Group unit-word-free-Group x) .x
      (left-unit-law-equiv-word-free-Group .x) =
      left-unit-law-mul-Group G _
    equiv-map-word-hom-universal-property-free-Group
      (mul-word-free-Group x unit-word-free-Group) .x
      (right-unit-law-equiv-word-free-Group .x) =
      right-unit-law-mul-Group G _
    equiv-map-word-hom-universal-property-free-Group
      (mul-word-free-Group (inv-word-free-Group x) .x) unit-word-free-Group
      (left-inverse-law-equiv-word-free-Group .x) =
      left-inverse-law-mul-Group G _
    equiv-map-word-hom-universal-property-free-Group
      (mul-word-free-Group x (inv-word-free-Group .x)) unit-word-free-Group
      (right-inverse-law-equiv-word-free-Group .x) =
      right-inverse-law-mul-Group G _

  reflecting-map-word-hom-universal-property-free-Group :
    reflecting-map-equivalence-relation
      ( equivalence-relation-word-free-Group A)
      ( type-Group G)
  reflecting-map-word-hom-universal-property-free-Group =
    ( map-word-hom-universal-property-free-Group ,
      rec-trunc-Prop
        ( Id-Prop (set-Group G) _ _)
        ( equiv-map-word-hom-universal-property-free-Group _ _))

  map-hom-universal-property-free-Group : type-free-Group A → type-Group G
  map-hom-universal-property-free-Group =
    inv-precomp-set-quotient
      ( equivalence-relation-word-free-Group A)
      ( set-Group G)
      ( reflecting-map-word-hom-universal-property-free-Group)

  abstract
    compute-map-hom-universal-property-free-Group :
      (x : word-free-Group A) →
      map-hom-universal-property-free-Group (in-word-free-Group A x) ＝
      map-word-hom-universal-property-free-Group x
    compute-map-hom-universal-property-free-Group =
      is-section-inv-precomp-set-quotient
        ( equivalence-relation-word-free-Group A)
        ( set-Group G)
        ( reflecting-map-word-hom-universal-property-free-Group)

    preserves-mul-map-hom-universal-property-free-Group :
      (x y : type-free-Group A) →
      map-hom-universal-property-free-Group (mul-free-Group A x y) ＝
      mul-Group G
        ( map-hom-universal-property-free-Group x)
        ( map-hom-universal-property-free-Group y)
    preserves-mul-map-hom-universal-property-free-Group =
      double-induction-set-quotient'
        ( equivalence-relation-word-free-Group A)
        ( λ x y →
          Id-Prop
            ( set-Group G)
            ( map-hom-universal-property-free-Group (mul-free-Group A x y))
            ( mul-Group G
              ( map-hom-universal-property-free-Group x)
              ( map-hom-universal-property-free-Group y)))
        ( λ x y →
          ( ap
            ( map-hom-universal-property-free-Group)
            ( compute-mul-free-Group A x y)) ∙
          ( compute-map-hom-universal-property-free-Group
            ( mul-word-free-Group x y)) ∙
          ( ap-mul-Group G
            ( inv (compute-map-hom-universal-property-free-Group x))
            ( inv (compute-map-hom-universal-property-free-Group y))))

  hom-universal-property-free-Group : hom-Group (free-Group A) G
  hom-universal-property-free-Group =
    ( map-hom-universal-property-free-Group ,
      preserves-mul-map-hom-universal-property-free-Group _ _)
```

#### Every homomorphism from the free group on `A` to `G` induces a map from `A` to `G`

```agda
module _
  {l1 l2 : Level}
  (A : UU l1)
  (G : Group l2)
  (f : hom-Group (free-Group A) G)
  where

  map-inv-hom-universal-property-free-Group : A → type-Group G
  map-inv-hom-universal-property-free-Group a =
    map-hom-Group (free-Group A) G f (in-free-Group A a)
```

#### The correspondence between homomorphisms from the free group on `A` to `G` and mappings from `A` to `G` is an equivalence

```agda
module _
  {l1 l2 : Level}
  (A : UU l1)
  (G : Group l2)
  where

  abstract
    compute-htpy-section-inv-universal-property-free-Group :
      (f : hom-Group (free-Group A) G) (x : word-free-Group A) →
      map-word-hom-universal-property-free-Group A G
        ( map-inv-hom-universal-property-free-Group A G f)
        ( x) ＝
      map-hom-Group (free-Group A) G f (in-word-free-Group A x)
    compute-htpy-section-inv-universal-property-free-Group
      f unit-word-free-Group =
      inv (preserves-unit-hom-Group (free-Group A) G f)
    compute-htpy-section-inv-universal-property-free-Group
      f (mul-word-free-Group x y) =
      ( ap-mul-Group G
        ( compute-htpy-section-inv-universal-property-free-Group f x)
        ( compute-htpy-section-inv-universal-property-free-Group f y)) ∙
      ( inv (preserves-mul-hom-Group (free-Group A) G f)) ∙
      ( ap
        ( map-hom-Group (free-Group A) G f)
        ( compute-mul-free-Group A x y))
    compute-htpy-section-inv-universal-property-free-Group
      f (inv-word-free-Group x) =
      ( ap
        ( inv-Group G)
        ( compute-htpy-section-inv-universal-property-free-Group f x)) ∙
      ( inv (preserves-inv-hom-Group (free-Group A) G f)) ∙
      ( ap
        ( map-hom-Group (free-Group A) G f)
        ( compute-inv-free-Group A x))
    compute-htpy-section-inv-universal-property-free-Group
      f (in-generator-word-free-Group x) =
      refl

    htpy-section-inv-universal-property-free-Group :
      (f : hom-Group (free-Group A) G) →
      htpy-hom-Group
        ( free-Group A)
        ( G)
        ( hom-universal-property-free-Group A G
          ( map-inv-hom-universal-property-free-Group A G f))
        ( f)
    htpy-section-inv-universal-property-free-Group f =
      induction-set-quotient
        ( equivalence-relation-word-free-Group A)
        ( λ x →
          Id-Prop
            ( set-Group G)
            ( map-hom-universal-property-free-Group A G
              ( map-inv-hom-universal-property-free-Group A G f)
              ( x))
            ( map-hom-Group (free-Group A) G f x))
        ( λ x →
          ( compute-map-hom-universal-property-free-Group A G _ x) ∙
          ( compute-htpy-section-inv-universal-property-free-Group f x))

    htpy-retraction-inv-universal-property-free-Group :
      (f : A → type-Group G) →
      map-inv-hom-universal-property-free-Group A G
        ( hom-universal-property-free-Group A G f) ~
      f
    htpy-retraction-inv-universal-property-free-Group f a =
      compute-map-hom-universal-property-free-Group
        ( A)
        ( G)
        ( f)
        ( in-generator-word-free-Group a)

    is-section-inv-universal-property-free-Group :
      is-section
        ( hom-universal-property-free-Group A G)
        ( map-inv-hom-universal-property-free-Group A G)
    is-section-inv-universal-property-free-Group f =
      eq-htpy-hom-Group
        ( free-Group A)
        ( G)
        ( htpy-section-inv-universal-property-free-Group f)

    is-retraction-inv-universal-property-free-Group :
      is-retraction
        ( hom-universal-property-free-Group A G)
        ( map-inv-hom-universal-property-free-Group A G)
    is-retraction-inv-universal-property-free-Group f =
      eq-htpy (htpy-retraction-inv-universal-property-free-Group f)

  is-equiv-hom-universal-property-free-Group :
    is-equiv (hom-universal-property-free-Group A G)
  is-equiv-hom-universal-property-free-Group =
    is-equiv-is-invertible
      ( map-inv-hom-universal-property-free-Group A G)
      ( is-section-inv-universal-property-free-Group)
      ( is-retraction-inv-universal-property-free-Group)

  universal-property-free-Group :
    (A → type-Group G) ≃ hom-Group (free-Group A) G
  universal-property-free-Group =
    ( hom-universal-property-free-Group A G ,
      is-equiv-hom-universal-property-free-Group)
```
