# Conjugation in groups

```agda
module group-theory.conjugation where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.transposition-identifications-along-retractions
open import foundation.transposition-identifications-along-sections
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.integer-powers-of-elements-groups
open import group-theory.isomorphisms-groups
open import group-theory.subsets-groups
```

</details>

## Idea

**Conjugation** by an element `x` of a [group](group-theory.groups.md) `G` is
the map `y ↦ (xy)x⁻¹`. This can be seen as a homomorphism `G → G` as well as a
group action of `G` onto itself.

The delooping of the conjugation homomorphism is defined in
[`structured-types.conjugation-pointed-types`](structured-types.conjugation-pointed-types.md).

## Definitions

### Conjugation

```agda
module _
  {l : Level} (G : Group l)
  where

  equiv-left-conjugation-Group :
    (x : type-Group G) → type-Group G ≃ type-Group G
  equiv-left-conjugation-Group x =
    equiv-mul-Group' G (inv-Group G x) ∘e equiv-mul-Group G x

  equiv-right-conjugation-Group :
    (x : type-Group G) → type-Group G ≃ type-Group G
  equiv-right-conjugation-Group x =
    equiv-mul-Group G x ∘e equiv-mul-Group' G (inv-Group G x)

  equiv-conjugation-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  equiv-conjugation-Group = equiv-left-conjugation-Group

  left-conjugation-Group : (x : type-Group G) → type-Group G → type-Group G
  left-conjugation-Group x = map-equiv (equiv-left-conjugation-Group x)

  right-conjugation-Group : (x : type-Group G) → type-Group G → type-Group G
  right-conjugation-Group x = map-equiv (equiv-right-conjugation-Group x)

  conjugation-Group : (x : type-Group G) → type-Group G → type-Group G
  conjugation-Group = left-conjugation-Group

  equiv-conjugation-Group' : (x : type-Group G) → type-Group G ≃ type-Group G
  equiv-conjugation-Group' x =
    equiv-mul-Group' G x ∘e equiv-mul-Group G (inv-Group G x)

  conjugation-Group' : (x : type-Group G) → type-Group G → type-Group G
  conjugation-Group' x = map-equiv (equiv-conjugation-Group' x)
```

### Left and right conjugation are equivalent

```agda
module _
  {l : Level} (G : Group l)
  where

  left-right-conjugation-Group :
    (x : type-Group G) →
    left-conjugation-Group G x ~ right-conjugation-Group G x
  left-right-conjugation-Group x y = associative-mul-Group G x y (inv-Group G x)
```

### The conjugation action of a group on itself

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  conjugation-action-Group : action-Group G l1
  pr1 conjugation-action-Group = set-Group G
  pr1 (pr2 conjugation-action-Group) g = equiv-conjugation-Group G g
  pr2 (pr2 conjugation-action-Group) {g} {h} =
    eq-htpy-equiv
      ( λ x →
        ( ap-mul-Group G
          ( associative-mul-Group G g h x)
          ( distributive-inv-mul-Group G)) ∙
        ( inv
          ( associative-mul-Group G
            ( mul-Group G g (mul-Group G h x))
            ( inv-Group G h)
            ( inv-Group G g))) ∙
        ( ap
          ( mul-Group' G (inv-Group G g))
          ( associative-mul-Group G g
            ( mul-Group G h x)
            ( inv-Group G h))))
```

### The predicate on subsets of groups of being closed under conjugation

```agda
module _
  {l1 l2 : Level} (G : Group l1) (S : subset-Group l2 G)
  where

  is-closed-under-conjugation-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-conjugation-subset-Group =
    (x y : type-Group G) →
    is-in-subtype S y → is-in-subtype S (conjugation-Group G x y)
```

## Properties

### Laws for conjugation and multiplication

```agda
module _
  {l : Level} (G : Group l)
  where

  conjugation-unit-Group :
    (x : type-Group G) → conjugation-Group G x (unit-Group G) ＝ unit-Group G
  conjugation-unit-Group x =
    ( ap (mul-Group' G (inv-Group G x)) (right-unit-law-mul-Group G x)) ∙
    ( right-inverse-law-mul-Group G x)

  compute-conjugation-unit-Group :
    conjugation-Group G (unit-Group G) ~ id
  compute-conjugation-unit-Group x =
    ( ap-mul-Group G (left-unit-law-mul-Group G x) (inv-unit-Group G)) ∙
    ( right-unit-law-mul-Group G x)

  compute-conjugation-mul-Group :
    (x y : type-Group G) →
    conjugation-Group G (mul-Group G x y) ~
    (conjugation-Group G x ∘ conjugation-Group G y)
  compute-conjugation-mul-Group x y z =
    ( ap-mul-Group G
      ( associative-mul-Group G x y z)
      ( distributive-inv-mul-Group G)) ∙
    ( inv
      ( associative-mul-Group G
        ( mul-Group G x (mul-Group G y z))
        ( inv-Group G y)
        ( inv-Group G x))) ∙
    ( ap
      ( mul-Group' G (inv-Group G x))
      ( associative-mul-Group G x (mul-Group G y z) (inv-Group G y)))

  compute-conjugation-mul-Group' :
    (x y : type-Group G) →
    conjugation-Group' G (mul-Group G x y) ~
    ( conjugation-Group' G y ∘ conjugation-Group' G x)
  compute-conjugation-mul-Group' x y z =
    ( ap
      ( mul-Group' G (mul-Group G x y))
      ( ( ap (mul-Group' G z) (distributive-inv-mul-Group G)) ∙
        ( associative-mul-Group G
          ( inv-Group G y)
          ( inv-Group G x)
          ( z)))) ∙
    ( associative-mul-Group G
      ( inv-Group G y)
      ( left-div-Group G x z)
      ( mul-Group G x y)) ∙
    ( ap
      ( left-div-Group G y)
      ( inv (associative-mul-Group G (left-div-Group G x z) x y))) ∙
    ( inv
      ( associative-mul-Group G
        ( inv-Group G y)
        ( conjugation-Group' G x z)
        ( y)))

  htpy-conjugation-Group :
    (x : type-Group G) →
    conjugation-Group' G x ~ conjugation-Group G (inv-Group G x)
  htpy-conjugation-Group x y =
    ap
      ( mul-Group G (mul-Group G (inv-Group G x) y))
      ( inv (inv-inv-Group G x))

  htpy-conjugation-Group' :
    (x : type-Group G) →
    conjugation-Group G x ~ conjugation-Group' G (inv-Group G x)
  htpy-conjugation-Group' x y =
    ap
      ( mul-Group' G (inv-Group G x))
      ( ap (mul-Group' G y) (inv (inv-inv-Group G x)))

  right-conjugation-law-mul-Group :
    (x y : type-Group G) →
    mul-Group G (inv-Group G x) (conjugation-Group G x y) ＝
    right-div-Group G y x
  right-conjugation-law-mul-Group x y =
    inv
      ( transpose-eq-mul-Group' G
        ( inv (associative-mul-Group G x y (inv-Group G x))))

  right-conjugation-law-mul-Group' :
    (x y : type-Group G) →
    mul-Group G x (conjugation-Group' G x y) ＝
    mul-Group G y x
  right-conjugation-law-mul-Group' x y =
    ( ap
      ( mul-Group G x)
      ( associative-mul-Group G (inv-Group G x) y x)) ∙
    ( is-section-left-div-Group G x (mul-Group G y x))

  left-conjugation-law-mul-Group :
    (x y : type-Group G) →
    mul-Group G (conjugation-Group G x y) x ＝ mul-Group G x y
  left-conjugation-law-mul-Group x y =
    ( associative-mul-Group G (mul-Group G x y) (inv-Group G x) x) ∙
    ( ap
      ( mul-Group G (mul-Group G x y))
      ( left-inverse-law-mul-Group G x)) ∙
    ( right-unit-law-mul-Group G (mul-Group G x y))

  left-conjugation-law-mul-Group' :
    (x y : type-Group G) →
    mul-Group G (conjugation-Group' G x y) (inv-Group G x) ＝
    left-div-Group G x y
  left-conjugation-law-mul-Group' x y =
    is-retraction-right-div-Group G x (mul-Group G (inv-Group G x) y)

  distributive-conjugation-mul-Group :
    (x y z : type-Group G) →
    conjugation-Group G x (mul-Group G y z) ＝
    mul-Group G (conjugation-Group G x y) (conjugation-Group G x z)
  distributive-conjugation-mul-Group x y z =
    ( ap
      ( mul-Group' G (inv-Group G x))
      ( ( inv (associative-mul-Group G x y z)) ∙
        ( ap
          ( mul-Group' G z)
          ( inv (is-section-right-div-Group G x (mul-Group G x y)))) ∙
        ( associative-mul-Group G
          ( conjugation-Group G x y)
          ( x)
          ( z)))) ∙
    ( associative-mul-Group G
      ( conjugation-Group G x y)
      ( mul-Group G x z)
      ( inv-Group G x))

  conjugation-inv-Group :
    (x y : type-Group G) →
    conjugation-Group G x (inv-Group G y) ＝
    inv-Group G (conjugation-Group G x y)
  conjugation-inv-Group x y =
    ( inv (inv-inv-Group G (conjugation-Group G x (inv-Group G y)))) ∙
    ( ap
      ( inv-Group G)
      ( ( distributive-inv-mul-Group G) ∙
        ( ap-mul-Group G
          ( inv-inv-Group G x)
          ( ( distributive-inv-mul-Group G) ∙
            ( ap
              ( mul-Group' G (inv-Group G x))
              ( inv-inv-Group G y)))) ∙
        ( inv (associative-mul-Group G x y ( inv-Group G x)))))

  conjugation-inv-Group' :
    (x y : type-Group G) →
    conjugation-Group' G x (inv-Group G y) ＝
    inv-Group G (conjugation-Group' G x y)
  conjugation-inv-Group' x y =
    ( ap (mul-Group' G x) (inv (distributive-inv-mul-Group G))) ∙
    ( ap
      ( mul-Group G (inv-Group G (mul-Group G y x)))
      ( inv (inv-inv-Group G x))) ∙
    ( inv
      ( distributive-inv-mul-Group G)) ∙
    ( ap
      ( inv-Group G)
      ( inv (associative-mul-Group G (inv-Group G x) y x)))

  conjugation-left-div-Group :
    (x y : type-Group G) →
    conjugation-Group G x (left-div-Group G x y) ＝
    right-div-Group G y x
  conjugation-left-div-Group x y =
    ap (λ y → right-div-Group G y x) (is-section-left-div-Group G x y)

  conjugation-left-div-Group' :
    (x y : type-Group G) →
    conjugation-Group G y (left-div-Group G x y) ＝
    right-div-Group G y x
  conjugation-left-div-Group' x y =
    ( ap
      ( λ z → right-div-Group G z y)
      ( inv (associative-mul-Group G y (inv-Group G x) y))) ∙
    ( is-retraction-right-div-Group G y (right-div-Group G y x))

  conjugation-right-div-Group :
    (x y : type-Group G) →
    conjugation-Group' G y (right-div-Group G x y) ＝
    left-div-Group G y x
  conjugation-right-div-Group x y =
    ( associative-mul-Group G
      ( inv-Group G y)
      ( right-div-Group G x y)
      ( y)) ∙
    ( ap (left-div-Group G y) (is-section-right-div-Group G y x))

  conjugation-right-div-Group' :
    (x y : type-Group G) →
    conjugation-Group' G x (right-div-Group G x y) ＝
    left-div-Group G y x
  conjugation-right-div-Group' x y =
    ap (mul-Group' G x) (is-retraction-left-div-Group G x (inv-Group G y))

  is-section-conjugation-inv-Group :
    (x : type-Group G) →
    ( conjugation-Group G x ∘ conjugation-Group G (inv-Group G x)) ~ id
  is-section-conjugation-inv-Group x y =
    ( ap
      ( mul-Group' G (inv-Group G x))
      ( ( ap (mul-Group G x) (associative-mul-Group G _ _ _)) ∙
        ( is-section-left-div-Group G x
          ( right-div-Group G y (inv-Group G x))))) ∙
    ( is-section-right-div-Group G (inv-Group G x) y)

  is-retraction-conjugation-inv-Group :
    (x : type-Group G) →
    ( conjugation-Group G (inv-Group G x) ∘ conjugation-Group G x) ~ id
  is-retraction-conjugation-inv-Group x y =
    ( ap
      ( mul-Group' G (inv-Group G (inv-Group G x)))
      ( ( ap (mul-Group G (inv-Group G x)) (associative-mul-Group G _ _ _)) ∙
        ( is-retraction-left-div-Group G x
          ( right-div-Group G y x)))) ∙
    ( is-retraction-right-div-Group G (inv-Group G x) y)

  transpose-eq-conjugation-Group :
    {x y z : type-Group G} →
    y ＝ conjugation-Group G (inv-Group G x) z → conjugation-Group G x y ＝ z
  transpose-eq-conjugation-Group {x} {y} {z} =
    eq-transpose-is-section
      ( conjugation-Group G x)
      ( conjugation-Group G (inv-Group G x))
      ( is-section-conjugation-inv-Group x)

  transpose-eq-conjugation-Group' :
    {x y z : type-Group G} →
    conjugation-Group G (inv-Group G x) y ＝ z → y ＝ conjugation-Group G x z
  transpose-eq-conjugation-Group' {x} {y} {z} =
    eq-transpose-is-section'
      ( conjugation-Group G x)
      ( conjugation-Group G (inv-Group G x))
      ( is-section-conjugation-inv-Group x)

  transpose-eq-conjugation-inv-Group :
    {x y z : type-Group G} →
    y ＝ conjugation-Group G x z → conjugation-Group G (inv-Group G x) y ＝ z
  transpose-eq-conjugation-inv-Group {x} {y} {z} =
    eq-transpose-is-retraction
      ( conjugation-Group G x)
      ( conjugation-Group G (inv-Group G x))
      ( is-retraction-conjugation-inv-Group x)

  transpose-eq-conjugation-inv-Group' :
    {x y z : type-Group G} →
    conjugation-Group G x y ＝ z → y ＝ conjugation-Group G (inv-Group G x) z
  transpose-eq-conjugation-inv-Group' {x} {y} {z} =
    eq-transpose-is-retraction'
      ( conjugation-Group G x)
      ( conjugation-Group G (inv-Group G x))
      ( is-retraction-conjugation-inv-Group x)
```

### Conjugation by `x` is an automorphism of `G`

```agda
module _
  {l : Level} (G : Group l)
  where

  conjugation-hom-Group : type-Group G → hom-Group G G
  pr1 (conjugation-hom-Group x) = conjugation-Group G x
  pr2 (conjugation-hom-Group x) = distributive-conjugation-mul-Group G x _ _

  conjugation-equiv-Group : type-Group G → equiv-Group G G
  pr1 (conjugation-equiv-Group x) = equiv-conjugation-Group G x
  pr2 (conjugation-equiv-Group x) = distributive-conjugation-mul-Group G x _ _

  conjugation-iso-Group : type-Group G → iso-Group G G
  conjugation-iso-Group x = iso-equiv-Group G G (conjugation-equiv-Group x)

  preserves-integer-powers-conjugation-Group :
    (k : ℤ) (g x : type-Group G) →
    conjugation-Group G g (integer-power-Group G k x) ＝
    integer-power-Group G k (conjugation-Group G g x)
  preserves-integer-powers-conjugation-Group k g =
    preserves-integer-powers-hom-Group G G (conjugation-hom-Group g) k
```

### Any group homomorphism preserves conjugation

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  preserves-conjugation-hom-Group :
    {x y : type-Group G} →
    map-hom-Group G H f (conjugation-Group G x y) ＝
    conjugation-Group H (map-hom-Group G H f x) (map-hom-Group G H f y)
  preserves-conjugation-hom-Group =
    ( preserves-right-div-hom-Group G H f) ∙
    ( ap (mul-Group' H _) (preserves-mul-hom-Group G H f))
```
