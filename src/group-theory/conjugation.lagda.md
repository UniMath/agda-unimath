# Conjugation in groups

```agda
module group-theory.conjugation where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
```

</details>

## Idea

Conjugation by an element `x` in a group `G` is the map `y ↦ (xy)x⁻¹`.

## Definition

### Conjugation

```agda
module _
  {l : Level} (G : Group l)
  where

  equiv-conjugation-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  equiv-conjugation-Group x =
    equiv-mul-Group' G (inv-Group G x) ∘e equiv-mul-Group G x

  conjugation-Group : (x : type-Group G) → type-Group G → type-Group G
  conjugation-Group x = map-equiv (equiv-conjugation-Group x)

  equiv-conjugation-Group' : (x : type-Group G) → type-Group G ≃ type-Group G
  equiv-conjugation-Group' x =
    equiv-mul-Group' G x ∘e equiv-mul-Group G (inv-Group G x)

  conjugation-Group' : (x : type-Group G) → type-Group G → type-Group G
  conjugation-Group' x = map-equiv (equiv-conjugation-Group' x)
```

### The conjugation action of a group on itself

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  conjugation-Abstract-Group-Action : Abstract-Group-Action G l1
  pr1 conjugation-Abstract-Group-Action = set-Group G
  pr1 (pr2 conjugation-Abstract-Group-Action) g = equiv-conjugation-Group G g
  pr2 (pr2 conjugation-Abstract-Group-Action) g h =
    eq-htpy-equiv
      ( λ x →
        ( ap-mul-Group G
          ( associative-mul-Group G g h x)
          ( distributive-inv-mul-Group G g h)) ∙
        ( ( inv
            ( associative-mul-Group G
              ( mul-Group G g (mul-Group G h x))
              ( inv-Group G h)
              ( inv-Group G g))) ∙
          ( ap
            ( mul-Group' G (inv-Group G g))
            ( associative-mul-Group G g
              ( mul-Group G h x)
              ( inv-Group G h)))))
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
    ( issec-mul-inv-Group G x (mul-Group G y x))

  left-conjugation-law-mul-Group :
    (x y : type-Group G) →
    mul-Group G (conjugation-Group G x y) x ＝ mul-Group G x y
  left-conjugation-law-mul-Group x y =
    ( associative-mul-Group G (mul-Group G x y) (inv-Group G x) x) ∙
    ( ( ap
        ( mul-Group G (mul-Group G x y))
        ( left-inverse-law-mul-Group G x)) ∙
      ( right-unit-law-mul-Group G (mul-Group G x y)))

  left-conjugation-law-mul-Group' :
    (x y : type-Group G) →
    mul-Group G (conjugation-Group' G x y) (inv-Group G x) ＝
    left-div-Group G x y
  left-conjugation-law-mul-Group' x y =
    isretr-mul-inv-Group' G x (mul-Group G (inv-Group G x) y)

  distributive-conjugation-mul-Group :
    (x y z : type-Group G) →
    conjugation-Group G x (mul-Group G y z) ＝
    mul-Group G (conjugation-Group G x y) (conjugation-Group G x z)
  distributive-conjugation-mul-Group x y z =
    ( ap
      ( mul-Group' G (inv-Group G x))
      ( ( ( inv (associative-mul-Group G x y z)) ∙
          ( ap
            ( mul-Group' G z)
            ( inv (issec-mul-inv-Group' G x (mul-Group G x y))))) ∙
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
      ( ( distributive-inv-mul-Group G
          ( mul-Group G x (inv-Group G y))
          ( inv-Group G x)) ∙
        ( ( ap-mul-Group G
            ( inv-inv-Group G x)
            ( ( distributive-inv-mul-Group G x (inv-Group G y)) ∙
              ( ap
                ( mul-Group' G (inv-Group G x))
                ( inv-inv-Group G y)))) ∙
          ( inv (associative-mul-Group G x y ( inv-Group G x))))))

  conjugation-inv-Group' :
    (x y : type-Group G) →
    conjugation-Group' G x (inv-Group G y) ＝
    inv-Group G (conjugation-Group' G x y)
  conjugation-inv-Group' x y =
    ( ap (mul-Group' G x) (inv (distributive-inv-mul-Group G y x))) ∙
    ( ( ap
        ( mul-Group G (inv-Group G (mul-Group G y x)))
        ( inv (inv-inv-Group G x))) ∙
      ( ( inv
          ( distributive-inv-mul-Group G
            ( inv-Group G x)
            ( mul-Group G y x))) ∙
        ( ap
          ( inv-Group G)
          ( inv (associative-mul-Group G (inv-Group G x) y x)))))

  conjugation-left-div-Group :
    (x y : type-Group G) →
    conjugation-Group G x (left-div-Group G x y) ＝
    right-div-Group G y x
  conjugation-left-div-Group x y =
    ap (mul-Group' G (inv-Group G x)) (issec-mul-inv-Group G x y)

  conjugation-left-div-Group' :
    (x y : type-Group G) →
    conjugation-Group G y (left-div-Group G x y) ＝
    right-div-Group G y x
  conjugation-left-div-Group' x y =
    ( ap
      ( mul-Group' G (inv-Group G y))
      ( inv (associative-mul-Group G y (inv-Group G x) y))) ∙
    ( isretr-mul-inv-Group' G y (right-div-Group G y x))

  conjugation-right-div-Group :
    (x y : type-Group G) →
    conjugation-Group' G y (right-div-Group G x y) ＝
    left-div-Group G y x
  conjugation-right-div-Group x y =
    ( associative-mul-Group G
      ( inv-Group G y)
      ( right-div-Group G x y)
      ( y)) ∙
    ( ap (mul-Group G (inv-Group G y)) (issec-mul-inv-Group' G y x))

  conjugation-right-div-Group' :
    (x y : type-Group G) →
    conjugation-Group' G x (right-div-Group G x y) ＝
    left-div-Group G y x
  conjugation-right-div-Group' x y =
    ap (mul-Group' G x) (isretr-mul-inv-Group G x (inv-Group G y))
```

### Conjugation by `x` is an automorphism of `G`

```agda
module _
  {l : Level} (G : Group l)
  where

  conjugation-hom-Group : type-Group G → type-hom-Group G G
  pr1 (conjugation-hom-Group x) = conjugation-Group G x
  pr2 (conjugation-hom-Group x) = distributive-conjugation-mul-Group G x

  conjugation-equiv-Group : type-Group G → equiv-Group G G
  pr1 (conjugation-equiv-Group x) = equiv-conjugation-Group G x
  pr2 (conjugation-equiv-Group x) = distributive-conjugation-mul-Group G x

  conjugation-iso-Group : type-Group G → type-iso-Group G G
  conjugation-iso-Group x = iso-equiv-Group G G (conjugation-equiv-Group x)
```
