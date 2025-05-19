# The Kleisli precategory of a monad

```agda
module category-theory.kleisli-precategory where
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

The {{#concept "Kleisli precategory"}} of a
[monad on a precategory](category-theory.monads-on-precategories) `T : C → C` is
the precategory of free `T`-algebras and their morphisms; we view it as the
precategory with the same objects as `C` but with morphisms `X → Y` the
morphisms `X → TY` in `C`. Composition is given by:

```text
     f       g        μZ
  X ---> TY ---> TTZ ---> TZ
```

It comes with functors to and from `C` which form an adjoint pair; the
composition recovers the original monad.

```agda
module _
  {l1 l2 : Level} {C : Precategory l1 l2}
  (T : monad-Precategory C)
  where

  private
    Tf = endofunctor-monad-Precategory C T
    μ = hom-mul-monad-Precategory C T
    η = hom-unit-monad-Precategory C T
    T₀ = obj-endofunctor-monad-Precategory C T
    T₁ = hom-endofunctor-monad-Precategory C T

  obj-kleisli-monad-Precategory : UU l1
  obj-kleisli-monad-Precategory = obj-Precategory C

  hom-set-kleisli-monad-Precategory :
    (x y : obj-kleisli-monad-Precategory) →
    Set l2
  hom-set-kleisli-monad-Precategory x y =
    hom-set-Precategory C x (obj-endofunctor-monad-Precategory C T y)

  hom-kleisli-monad-Precategory :
    (x y : obj-kleisli-monad-Precategory) →
    UU l2
  hom-kleisli-monad-Precategory x y =
    type-Set (hom-set-kleisli-monad-Precategory x y)

  id-hom-kleisli-monad-Precategory :
    (x : obj-kleisli-monad-Precategory) →
    hom-kleisli-monad-Precategory x x
  id-hom-kleisli-monad-Precategory x = hom-unit-monad-Precategory C T x

  comp-hom-kleisli-monad-Precategory :
    {x y z : obj-kleisli-monad-Precategory}
    (g : hom-kleisli-monad-Precategory y z)
    (f : hom-kleisli-monad-Precategory x y) →
    hom-kleisli-monad-Precategory x z
  comp-hom-kleisli-monad-Precategory g f =
    comp-hom-Precategory C (comp-hom-Precategory C (μ _) (T₁ g)) f

  associative-comp-hom-kleisli-monad-Precategory :
    {x y z w : obj-kleisli-monad-Precategory}
    (h : hom-kleisli-monad-Precategory z w)
    (g : hom-kleisli-monad-Precategory y z)
    (f : hom-kleisli-monad-Precategory x y) →
    (comp-hom-kleisli-monad-Precategory
      ( comp-hom-kleisli-monad-Precategory h g)
      ( f)) ＝
    (comp-hom-kleisli-monad-Precategory
      ( h)
      ( comp-hom-kleisli-monad-Precategory g f))
  associative-comp-hom-kleisli-monad-Precategory h g f =
    ap
      ( precomp-hom-Precategory C f _)
      ( (ap
          ( postcomp-hom-Precategory C (μ _) _)
          ( (preserves-comp-endofunctor-monad-Precategory C T _ g) ∙
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
          ( (inv (associative-comp-hom-Precategory C _ _ _)) ∙
            (ap
              ( precomp-hom-Precategory C (T₁ g) _)
              ( inv (naturality-mul-monad-Precategory C T h))) ∙
            ( associative-comp-hom-Precategory C _ _ _))) ∙
        ( inv (associative-comp-hom-Precategory C _ _ _))) ∙
    ( associative-comp-hom-Precategory C _ _ _)

  left-unit-law-comp-hom-kleisli-monad-Precategory :
    {x y : obj-kleisli-monad-Precategory}
    (f : hom-kleisli-monad-Precategory x y) →
    ( comp-hom-kleisli-monad-Precategory
      ( id-hom-kleisli-monad-Precategory y)
      ( f)) ＝
    ( f)
  left-unit-law-comp-hom-kleisli-monad-Precategory f =
    ( ap
      ( precomp-hom-Precategory C _ _)
      ( left-unit-law-mul-hom-family-monad-Precategory C T _)) ∙
    ( left-unit-law-comp-hom-Precategory C f)

  right-unit-law-comp-hom-kleisli-monad-Precategory :
    {x y : obj-kleisli-monad-Precategory}
    (f : hom-kleisli-monad-Precategory x y) →
    ( comp-hom-kleisli-monad-Precategory
      ( f)
      ( id-hom-kleisli-monad-Precategory x)) ＝
    ( f)
  right-unit-law-comp-hom-kleisli-monad-Precategory f =
    (associative-comp-hom-Precategory C _ _ _) ∙
    (ap
      (postcomp-hom-Precategory C _ _)
      (naturality-unit-monad-Precategory C T f)) ∙
    (inv (associative-comp-hom-Precategory C _ _ _)) ∙
    (ap
      (precomp-hom-Precategory C f _)
      (right-unit-law-mul-hom-family-monad-Precategory C T _)) ∙
    (left-unit-law-comp-hom-Precategory C f)

  kleisli-monad-Precategory : Precategory l1 l2
  kleisli-monad-Precategory =
    make-Precategory
      ( obj-kleisli-monad-Precategory)
      ( hom-set-kleisli-monad-Precategory)
      ( comp-hom-kleisli-monad-Precategory)
      ( id-hom-kleisli-monad-Precategory)
      ( associative-comp-hom-kleisli-monad-Precategory)
      ( left-unit-law-comp-hom-kleisli-monad-Precategory)
      ( right-unit-law-comp-hom-kleisli-monad-Precategory)

  obj-functor-to-kleisli-monad-Precategory :
    (obj-Precategory C) → obj-kleisli-monad-Precategory
  obj-functor-to-kleisli-monad-Precategory = id

  hom-functor-to-kleisli-monad-Precategory :
    {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    hom-kleisli-monad-Precategory
      ( obj-functor-to-kleisli-monad-Precategory x)
      ( obj-functor-to-kleisli-monad-Precategory y)
  hom-functor-to-kleisli-monad-Precategory {x} {y} f =
    comp-hom-Precategory C
      ( T₁ f)
      ( hom-unit-monad-Precategory C T x)

  preserves-id-functor-to-kleisli-monad-Precategory :
    (x : obj-Precategory C) →
    ( hom-functor-to-kleisli-monad-Precategory
      ( id-hom-Precategory C {x})) ＝
    ( id-hom-kleisli-monad-Precategory _)
  preserves-id-functor-to-kleisli-monad-Precategory x =
    ( ap
      ( precomp-hom-Precategory C _ _)
      ( preserves-id-endofunctor-monad-Precategory C T x)) ∙
    ( left-unit-law-comp-hom-Precategory C _)

  preserves-comp-functor-to-kleisli-monad-Precategory :
    {x y z : obj-Precategory C} →
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    hom-functor-to-kleisli-monad-Precategory (comp-hom-Precategory C g f) ＝
    comp-hom-kleisli-monad-Precategory
      ( hom-functor-to-kleisli-monad-Precategory g)
      ( hom-functor-to-kleisli-monad-Precategory f)
  preserves-comp-functor-to-kleisli-monad-Precategory {x} {y} {z} g f =
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
              ( (inv
                  (preserves-comp-endofunctor-monad-Precategory C T
                    (η z) g)) ∙
                ( ap
                  ( T₁)
                  ( inv (naturality-unit-monad-Precategory C T g))))))))) ∙
    ( associative-comp-hom-Precategory C _ _ _)

  functor-to-kleisli-monad-Precategory :
    functor-Precategory C kleisli-monad-Precategory
  functor-to-kleisli-monad-Precategory =
    obj-functor-to-kleisli-monad-Precategory ,
    hom-functor-to-kleisli-monad-Precategory ,
    preserves-comp-functor-to-kleisli-monad-Precategory ,
    preserves-id-functor-to-kleisli-monad-Precategory

  obj-functor-from-kleisli-monad-Precategory :
    obj-kleisli-monad-Precategory → obj-Precategory C
  obj-functor-from-kleisli-monad-Precategory = T₀

  hom-functor-from-kleisli-monad-Precategory :
    {x y : obj-kleisli-monad-Precategory}
    (f : hom-kleisli-monad-Precategory x y) →
    hom-Precategory C
      ( obj-functor-from-kleisli-monad-Precategory x)
      ( obj-functor-from-kleisli-monad-Precategory y)
  hom-functor-from-kleisli-monad-Precategory {x} {y} f =
    comp-hom-Precategory C (hom-mul-monad-Precategory C T y) (T₁ f)

  preserves-id-functor-from-kleisli-monad-Precategory :
    (x : obj-kleisli-monad-Precategory) →
    hom-functor-from-kleisli-monad-Precategory
      ( id-hom-kleisli-monad-Precategory x) ＝
    id-hom-Precategory C {obj-functor-from-kleisli-monad-Precategory x}
  preserves-id-functor-from-kleisli-monad-Precategory =
    left-unit-law-mul-hom-family-monad-Precategory C T

  preserves-comp-functor-from-kleisli-monad-Precategory :
    {x y z : obj-kleisli-monad-Precategory}
    (g : hom-kleisli-monad-Precategory y z)
    (f : hom-kleisli-monad-Precategory x y) →
    hom-functor-from-kleisli-monad-Precategory
      ( comp-hom-kleisli-monad-Precategory g f) ＝
    comp-hom-Precategory C
      ( hom-functor-from-kleisli-monad-Precategory g)
      ( hom-functor-from-kleisli-monad-Precategory f)
  preserves-comp-functor-from-kleisli-monad-Precategory {x} {y} {z} g f =
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

  functor-from-kleisli-monad-Precategory :
    functor-Precategory kleisli-monad-Precategory C
  functor-from-kleisli-monad-Precategory =
    ( obj-functor-from-kleisli-monad-Precategory) ,
    ( hom-functor-from-kleisli-monad-Precategory) ,
    ( preserves-comp-functor-from-kleisli-monad-Precategory) ,
    ( preserves-id-functor-from-kleisli-monad-Precategory)
```
