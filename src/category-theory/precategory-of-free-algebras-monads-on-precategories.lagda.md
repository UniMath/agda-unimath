# The precategory of free algebras of a monad

```agda
module category-theory.precategory-of-free-algebras-monads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.monads-on-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

The
{{#concept "precategory of free algebras" Disambiguation="of a monad on a precategory" Agda=free-algebras-monad-Precategory WDID=Q1773982 WD="Kleisli category"}}
of a [monad on a precategory](category-theory.monads-on-precategories.md)
`T : C → C`, also called the **Kleisli precategory**, is the precategory of free
`T`-algebras and their morphisms; we view it as the precategory with the same
objects as `C` but with morphisms `X → Y` the morphisms `X → TY` in `C`.
Composition is given by:

```text
     f       g        μZ
  X ---> TY ---> TTZ ---> TZ
```

It comes with functors to and from `C` which form an adjoint pair; the
composition recovers the original monad.

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  (let μ = hom-mul-monad-Precategory C T)
  (let η = hom-unit-monad-Precategory C T)
  (let T₁ = hom-endofunctor-monad-Precategory C T)
  where

  obj-free-algebras-monad-Precategory : UU l1
  obj-free-algebras-monad-Precategory = obj-Precategory C

  hom-set-free-algebras-monad-Precategory :
    (x y : obj-free-algebras-monad-Precategory) →
    Set l2
  hom-set-free-algebras-monad-Precategory x y =
    hom-set-Precategory C x (obj-endofunctor-monad-Precategory C T y)

  hom-free-algebras-monad-Precategory :
    (x y : obj-free-algebras-monad-Precategory) →
    UU l2
  hom-free-algebras-monad-Precategory x y =
    type-Set (hom-set-free-algebras-monad-Precategory x y)

  id-hom-free-algebras-monad-Precategory :
    (x : obj-free-algebras-monad-Precategory) →
    hom-free-algebras-monad-Precategory x x
  id-hom-free-algebras-monad-Precategory x = hom-unit-monad-Precategory C T x

  comp-hom-free-algebras-monad-Precategory :
    {x y z : obj-free-algebras-monad-Precategory}
    (g : hom-free-algebras-monad-Precategory y z)
    (f : hom-free-algebras-monad-Precategory x y) →
    hom-free-algebras-monad-Precategory x z
  comp-hom-free-algebras-monad-Precategory g f =
    comp-hom-Precategory C (comp-hom-Precategory C (μ _) (T₁ g)) f

  associative-comp-hom-free-algebras-monad-Precategory :
    {x y z w : obj-free-algebras-monad-Precategory}
    (h : hom-free-algebras-monad-Precategory z w)
    (g : hom-free-algebras-monad-Precategory y z)
    (f : hom-free-algebras-monad-Precategory x y) →
    ( comp-hom-free-algebras-monad-Precategory
      ( comp-hom-free-algebras-monad-Precategory h g)
      ( f)) ＝
    ( comp-hom-free-algebras-monad-Precategory
      ( h)
      ( comp-hom-free-algebras-monad-Precategory g f))
  associative-comp-hom-free-algebras-monad-Precategory h g f =
    ( ap
      ( precomp-hom-Precategory C f _)
      ( ( ap
          ( postcomp-hom-Precategory C (μ _) _)
          ( ( preserves-comp-endofunctor-monad-Precategory C T _ g) ∙
            ( ap
              ( precomp-hom-Precategory C (T₁ g) _)
              ( preserves-comp-endofunctor-monad-Precategory C T _ _)) ∙
            ( associative-comp-hom-Precategory C _ _ _))) ∙
        ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
        ( ap
          ( precomp-hom-Precategory C _ _)
          ( associative-mul-hom-family-monad-Precategory C T _)) ∙
        ( associative-comp-hom-Precategory C _ _ _) ∙
        ( ap
          ( postcomp-hom-Precategory C (μ _) _)
          ( ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
            ( ap
              ( precomp-hom-Precategory C (T₁ g) _)
              ( inv (naturality-mul-monad-Precategory C T h))) ∙
            ( associative-comp-hom-Precategory C _ _ _))) ∙
        ( inv (associative-comp-hom-Precategory C _ _ _)))) ∙
    ( associative-comp-hom-Precategory C _ _ _)

  left-unit-law-comp-hom-free-algebras-monad-Precategory :
    {x y : obj-free-algebras-monad-Precategory}
    (f : hom-free-algebras-monad-Precategory x y) →
    ( comp-hom-free-algebras-monad-Precategory
      ( id-hom-free-algebras-monad-Precategory y)
      ( f)) ＝
    ( f)
  left-unit-law-comp-hom-free-algebras-monad-Precategory f =
    ( ap
      ( precomp-hom-Precategory C _ _)
      ( left-unit-law-mul-hom-family-monad-Precategory C T _)) ∙
    ( left-unit-law-comp-hom-Precategory C f)

  right-unit-law-comp-hom-free-algebras-monad-Precategory :
    {x y : obj-free-algebras-monad-Precategory}
    (f : hom-free-algebras-monad-Precategory x y) →
    ( comp-hom-free-algebras-monad-Precategory
      ( f)
      ( id-hom-free-algebras-monad-Precategory x)) ＝
    ( f)
  right-unit-law-comp-hom-free-algebras-monad-Precategory f =
    ( associative-comp-hom-Precategory C _ _ _) ∙
    ( ap
      ( postcomp-hom-Precategory C _ _)
      ( naturality-unit-monad-Precategory C T f)) ∙
    ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
    ( ap
      ( precomp-hom-Precategory C f _)
      ( right-unit-law-mul-hom-family-monad-Precategory C T _)) ∙
    ( left-unit-law-comp-hom-Precategory C f)

  free-algebras-monad-Precategory : Precategory l1 l2
  free-algebras-monad-Precategory =
    make-Precategory
      ( obj-free-algebras-monad-Precategory)
      ( hom-set-free-algebras-monad-Precategory)
      ( comp-hom-free-algebras-monad-Precategory)
      ( id-hom-free-algebras-monad-Precategory)
      ( associative-comp-hom-free-algebras-monad-Precategory)
      ( left-unit-law-comp-hom-free-algebras-monad-Precategory)
      ( right-unit-law-comp-hom-free-algebras-monad-Precategory)
```

## Properties

### Free functor from the underlying category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  (let μ = hom-mul-monad-Precategory C T)
  (let η = hom-unit-monad-Precategory C T)
  (let T₁ = hom-endofunctor-monad-Precategory C T)
  where

  obj-functor-to-free-algebras-monad-Precategory :
    obj-Precategory C → obj-free-algebras-monad-Precategory C T
  obj-functor-to-free-algebras-monad-Precategory = id

  hom-functor-to-free-algebras-monad-Precategory :
    {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    hom-free-algebras-monad-Precategory C T
      ( obj-functor-to-free-algebras-monad-Precategory x)
      ( obj-functor-to-free-algebras-monad-Precategory y)
  hom-functor-to-free-algebras-monad-Precategory {x} {y} f =
    comp-hom-Precategory C
      ( T₁ f)
      ( hom-unit-monad-Precategory C T x)

  preserves-id-functor-to-free-algebras-monad-Precategory :
    (x : obj-Precategory C) →
    ( hom-functor-to-free-algebras-monad-Precategory
      ( id-hom-Precategory C {x})) ＝
    ( id-hom-free-algebras-monad-Precategory C T _)
  preserves-id-functor-to-free-algebras-monad-Precategory x =
    ( ap
      ( precomp-hom-Precategory C _ _)
      ( preserves-id-endofunctor-monad-Precategory C T x)) ∙
    ( left-unit-law-comp-hom-Precategory C _)

  preserves-comp-functor-to-free-algebras-monad-Precategory :
    {x y z : obj-Precategory C} →
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    hom-functor-to-free-algebras-monad-Precategory
      ( comp-hom-Precategory C g f) ＝
    comp-hom-free-algebras-monad-Precategory C T
      ( hom-functor-to-free-algebras-monad-Precategory g)
      ( hom-functor-to-free-algebras-monad-Precategory f)
  preserves-comp-functor-to-free-algebras-monad-Precategory {x} {y} {z} g f =
    ( ap
      ( precomp-hom-Precategory C (η x) _)
      ( ( preserves-comp-endofunctor-monad-Precategory C T g f) ∙
        ( ap
          ( precomp-hom-Precategory C (T₁ f) _)
          ( ( inv (left-unit-law-comp-hom-Precategory C _)) ∙
            ( ap
              ( precomp-hom-Precategory C (T₁ g) _)
              ( inv (left-unit-law-mul-hom-family-monad-Precategory C T z))) ∙
            ( associative-comp-hom-Precategory C _ _ _) ∙
            ( ap
              ( postcomp-hom-Precategory C (μ z) _)
              ( ( inv
                  ( preserves-comp-endofunctor-monad-Precategory C T
                    (η z) g)) ∙
                ( ap
                  ( T₁)
                  ( inv (naturality-unit-monad-Precategory C T g))))))))) ∙
    ( associative-comp-hom-Precategory C _ _ _)

  functor-to-free-algebras-monad-Precategory :
    functor-Precategory C (free-algebras-monad-Precategory C T)
  functor-to-free-algebras-monad-Precategory =
    ( obj-functor-to-free-algebras-monad-Precategory) ,
    ( hom-functor-to-free-algebras-monad-Precategory) ,
    ( preserves-comp-functor-to-free-algebras-monad-Precategory) ,
    ( preserves-id-functor-to-free-algebras-monad-Precategory)
```

### Forgetful functor to the underlying category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  (let μ = hom-mul-monad-Precategory C T)
  (let T₀ = obj-endofunctor-monad-Precategory C T)
  (let T₁ = hom-endofunctor-monad-Precategory C T)
  where

  obj-functor-from-free-algebras-monad-Precategory :
    obj-free-algebras-monad-Precategory C T → obj-Precategory C
  obj-functor-from-free-algebras-monad-Precategory = T₀

  hom-functor-from-free-algebras-monad-Precategory :
    {x y : obj-free-algebras-monad-Precategory C T}
    (f : hom-free-algebras-monad-Precategory C T x y) →
    hom-Precategory C
      ( obj-functor-from-free-algebras-monad-Precategory x)
      ( obj-functor-from-free-algebras-monad-Precategory y)
  hom-functor-from-free-algebras-monad-Precategory {x} {y} f =
    comp-hom-Precategory C (hom-mul-monad-Precategory C T y) (T₁ f)

  preserves-id-functor-from-free-algebras-monad-Precategory :
    (x : obj-free-algebras-monad-Precategory C T) →
    hom-functor-from-free-algebras-monad-Precategory
      ( id-hom-free-algebras-monad-Precategory C T x) ＝
    id-hom-Precategory C {obj-functor-from-free-algebras-monad-Precategory x}
  preserves-id-functor-from-free-algebras-monad-Precategory =
    left-unit-law-mul-hom-family-monad-Precategory C T

  preserves-comp-functor-from-free-algebras-monad-Precategory :
    {x y z : obj-free-algebras-monad-Precategory C T}
    (g : hom-free-algebras-monad-Precategory C T y z)
    (f : hom-free-algebras-monad-Precategory C T x y) →
    hom-functor-from-free-algebras-monad-Precategory
      ( comp-hom-free-algebras-monad-Precategory C T g f) ＝
    comp-hom-Precategory C
      ( hom-functor-from-free-algebras-monad-Precategory g)
      ( hom-functor-from-free-algebras-monad-Precategory f)
  preserves-comp-functor-from-free-algebras-monad-Precategory {x} {y} {z} g f =
    ( ap
      ( postcomp-hom-Precategory C (μ z) _)
      ( ( preserves-comp-endofunctor-monad-Precategory C T _ f) ∙
        ( ap
          ( precomp-hom-Precategory C (T₁ f) _)
          ( preserves-comp-endofunctor-monad-Precategory C T (μ z) (T₁ g))) ∙
        ( associative-comp-hom-Precategory C _ _ _))) ∙
    ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
    ( ap
      ( precomp-hom-Precategory C _ _)
      ( associative-mul-hom-family-monad-Precategory C T z)) ∙
    ( associative-comp-hom-Precategory C _ _ _) ∙
    ( ap
      ( postcomp-hom-Precategory C (μ z) _)
      ( ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
        ( ap
          ( precomp-hom-Precategory C (T₁ f) _)
          ( inv (naturality-mul-monad-Precategory C T g))) ∙
        ( associative-comp-hom-Precategory C _ _ _))) ∙
    ( inv (associative-comp-hom-Precategory C _ _ _))

  functor-from-free-algebras-monad-Precategory :
    functor-Precategory (free-algebras-monad-Precategory C T) C
  functor-from-free-algebras-monad-Precategory =
    ( obj-functor-from-free-algebras-monad-Precategory) ,
    ( hom-functor-from-free-algebras-monad-Precategory) ,
    ( preserves-comp-functor-from-free-algebras-monad-Precategory) ,
    ( preserves-id-functor-from-free-algebras-monad-Precategory)
```
