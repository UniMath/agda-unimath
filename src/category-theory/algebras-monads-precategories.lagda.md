# The Eilenberg-Moore precategory

```agda
module category-theory.algebras-monads-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-precategories
open import category-theory.functors-precategories
open import category-theory.monads-on-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The
{{#concept "category of algebras" Disambiguation="of a monad on a precategory" Agda=algebras-monad-Precategory}}
of a [monad on a precategory](category-theory.monads-on-precategories) `T`,
denoted `EM(T)`, also called the Eilenberg-Moore category, consists of all
`T`-algebras and `T`-algebra morphisms. It comes with an adjunction `C ⇄ EM(T)`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  (let Tf = endofunctor-monad-Precategory C T)
  (let T₁ = hom-endofunctor-monad-Precategory C T)
  (let T₀ = obj-endofunctor-monad-Precategory C T)
  where

  obj-algebras-monad-Precategory :
    UU (l1 ⊔ l2)
  obj-algebras-monad-Precategory = monad-algebra-Precategory C T

  hom-set-algebras-monad-Precategory :
    (a b : obj-algebras-monad-Precategory) →
    Set l2
  hom-set-algebras-monad-Precategory a b =
    ( morphism-monad-algebra-Precategory C T a b) ,
    ( is-set-morphism-monad-algebra-Precategory C T a b)

  hom-algebras-monad-Precategory :
    (a b : obj-algebras-monad-Precategory) →
    UU l2
  hom-algebras-monad-Precategory a b =
    type-Set (hom-set-algebras-monad-Precategory a b)

  comp-hom-algebras-monad-Precategory :
    (a b c : obj-algebras-monad-Precategory)
    (g : hom-algebras-monad-Precategory b c)
    (f : hom-algebras-monad-Precategory a b) →
    hom-algebras-monad-Precategory a c
  comp-hom-algebras-monad-Precategory a b c g f =
    comp-morphism-monad-algebra-Precategory C T a b c g f

  id-hom-algebras-monad-Precategory :
    (x : obj-algebras-monad-Precategory) →
    hom-algebras-monad-Precategory x x
  id-hom-algebras-monad-Precategory x =
    ( id-hom-Precategory C) ,
    ( left-unit-law-comp-hom-Precategory C
      ( hom-monad-algebra-Precategory C T x)) ∙
    ( inv
      ( right-unit-law-comp-hom-Precategory C
        ( hom-monad-algebra-Precategory C T x))) ∙
    ( ap
      ( postcomp-hom-Precategory C _ _)
      ( inv (preserves-id-endofunctor-monad-Precategory C T _)))

  associative-comp-hom-algebras-monad-Precategory :
    (x y z w : obj-algebras-monad-Precategory)
    (h : hom-algebras-monad-Precategory z w)
    (g : hom-algebras-monad-Precategory y z)
    (f : hom-algebras-monad-Precategory x y) →
    (comp-hom-algebras-monad-Precategory x y w
      ( comp-hom-algebras-monad-Precategory y z w h g)
      ( f)) ＝
    (comp-hom-algebras-monad-Precategory x z w
      ( h)
      ( comp-hom-algebras-monad-Precategory x y z g f))
  associative-comp-hom-algebras-monad-Precategory x y z w h g f =
    eq-pair-Σ
      ( associative-comp-hom-Precategory C _ _ _)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  left-unit-law-comp-hom-algebras-monad-Precategory :
    (a b : obj-algebras-monad-Precategory)
    (f : hom-algebras-monad-Precategory a b) →
    ( comp-hom-algebras-monad-Precategory a b b
      ( id-hom-algebras-monad-Precategory b)
      ( f)) ＝
    ( f)
  left-unit-law-comp-hom-algebras-monad-Precategory a b f =
    eq-pair-Σ
      ( left-unit-law-comp-hom-Precategory C
        ( hom-morphism-monad-algebra-Precategory C T a b f))
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  right-unit-law-comp-hom-algebras-monad-Precategory :
    (a b : obj-algebras-monad-Precategory)
    (f : hom-algebras-monad-Precategory a b) →
    ( comp-hom-algebras-monad-Precategory a a b
      ( f)
      ( id-hom-algebras-monad-Precategory a)) ＝
    ( f)
  right-unit-law-comp-hom-algebras-monad-Precategory a b f =
    eq-pair-Σ
      ( right-unit-law-comp-hom-Precategory C
        ( hom-morphism-monad-algebra-Precategory C T a b f))
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  algebras-monad-Precategory : Precategory (l1 ⊔ l2) l2
  algebras-monad-Precategory =
    make-Precategory
      ( obj-algebras-monad-Precategory)
      ( hom-set-algebras-monad-Precategory)
      ( λ {a} {b} {c} g f → comp-hom-algebras-monad-Precategory a b c g f)
      ( id-hom-algebras-monad-Precategory)
      ( λ {a} {b} {c} {d} h g f →
        ( associative-comp-hom-algebras-monad-Precategory a b c d h g f))
      ( λ {a} {b} f → left-unit-law-comp-hom-algebras-monad-Precategory a b f)
      ( λ {a} {b} f → right-unit-law-comp-hom-algebras-monad-Precategory a b f)

  obj-functor-to-algebras-monad-Precategory :
    obj-Precategory C → obj-Precategory algebras-monad-Precategory
  obj-functor-to-algebras-monad-Precategory x =
    ( obj-endofunctor-monad-Precategory C T x) ,
    ( ( hom-mul-monad-Precategory C T x) ,
      ( right-unit-law-mul-hom-family-monad-Precategory C T x) ,
      ( associative-mul-hom-family-monad-Precategory C T x))

  hom-functor-to-algebras-monad-Precategory : {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    hom-Precategory algebras-monad-Precategory
      ( obj-functor-to-algebras-monad-Precategory x)
      ( obj-functor-to-algebras-monad-Precategory y)
  hom-functor-to-algebras-monad-Precategory f =
    ( T₁ f) ,
    ( naturality-mul-monad-Precategory C T f)

  preserves-id-functor-to-algebras-monad-Precategory :
    (x : obj-Precategory C) →
    hom-functor-to-algebras-monad-Precategory (id-hom-Precategory C {x}) ＝
    id-hom-algebras-monad-Precategory
      ( obj-functor-to-algebras-monad-Precategory x)
  preserves-id-functor-to-algebras-monad-Precategory x =
    eq-pair-Σ
      ( preserves-id-endofunctor-monad-Precategory C T x)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  preserves-comp-functor-to-algebras-monad-Precategory :
    {x y z : obj-Precategory C} →
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    hom-functor-to-algebras-monad-Precategory (comp-hom-Precategory C g f) ＝
    comp-hom-algebras-monad-Precategory
      ( obj-functor-to-algebras-monad-Precategory x)
      ( obj-functor-to-algebras-monad-Precategory y)
      ( obj-functor-to-algebras-monad-Precategory z)
      ( hom-functor-to-algebras-monad-Precategory g)
      ( hom-functor-to-algebras-monad-Precategory f)
  preserves-comp-functor-to-algebras-monad-Precategory g f =
    eq-pair-Σ
      ( preserves-comp-endofunctor-monad-Precategory C T g f)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  functor-to-algebras-monad-Precategory :
    functor-Precategory C algebras-monad-Precategory
  functor-to-algebras-monad-Precategory =
    ( obj-functor-to-algebras-monad-Precategory) ,
    ( hom-functor-to-algebras-monad-Precategory) ,
    ( preserves-comp-functor-to-algebras-monad-Precategory) ,
    ( preserves-id-functor-to-algebras-monad-Precategory)

  obj-functor-from-algebras-monad-Precategory :
    obj-Precategory algebras-monad-Precategory → obj-Precategory C
  obj-functor-from-algebras-monad-Precategory =
    obj-monad-algebra-Precategory C T

  hom-functor-from-algebras-monad-Precategory :
    (x y : obj-algebras-monad-Precategory)
    (f : hom-algebras-monad-Precategory x y) →
    hom-Precategory C
      ( obj-functor-from-algebras-monad-Precategory x)
      ( obj-functor-from-algebras-monad-Precategory y)
  hom-functor-from-algebras-monad-Precategory =
    hom-morphism-monad-algebra-Precategory C T

  preserves-id-functor-from-algebras-monad-Precategory :
    (x : obj-algebras-monad-Precategory) →
    hom-functor-from-algebras-monad-Precategory x x
      ( id-hom-algebras-monad-Precategory x) ＝
    id-hom-Precategory C
  preserves-id-functor-from-algebras-monad-Precategory x = refl

  preserves-comp-functor-from-algebras-monad-Precategory :
    (x y z : obj-algebras-monad-Precategory)
    (g : hom-algebras-monad-Precategory y z)
    (f : hom-algebras-monad-Precategory x y) →
    hom-functor-from-algebras-monad-Precategory x z
      ( comp-hom-algebras-monad-Precategory x y z g f) ＝
    comp-hom-Precategory C
      ( hom-functor-from-algebras-monad-Precategory y z g)
      ( hom-functor-from-algebras-monad-Precategory x y f)
  preserves-comp-functor-from-algebras-monad-Precategory x y z g f = refl

  functor-from-algebras-monad-Precategory :
    functor-Precategory algebras-monad-Precategory C
  functor-from-algebras-monad-Precategory =
    ( obj-functor-from-algebras-monad-Precategory) ,
    ( λ {x} {y} f → hom-functor-from-algebras-monad-Precategory x y f) ,
    ( λ {x} {y} {z} g f →
      preserves-comp-functor-from-algebras-monad-Precategory x y z g f) ,
    ( preserves-id-functor-from-algebras-monad-Precategory)
```

The unit of the adjunction between these two functors is exactly the unit of the
monad.

```agda
  unit-algebras-monad-Precategory :
    natural-transformation-Precategory C C
      ( id-functor-Precategory C)
      ( comp-functor-Precategory C algebras-monad-Precategory C
        ( functor-from-algebras-monad-Precategory)
        ( functor-to-algebras-monad-Precategory))
  unit-algebras-monad-Precategory = unit-monad-Precategory C T
```

The counit is the vertical map given by the structure map of the algebra

```text
          μ
    T²x ----> Tx
     |         |
  Ta |         | a
     ∨         ∨
     Tx -----> x.
          a
```

```agda
  counit-algebras-monad-Precategory :
    natural-transformation-Precategory
      ( algebras-monad-Precategory)
      ( algebras-monad-Precategory)
      ( comp-functor-Precategory
        ( algebras-monad-Precategory)
        ( C)
        ( algebras-monad-Precategory)
        ( functor-to-algebras-monad-Precategory)
        ( functor-from-algebras-monad-Precategory))
      ( id-functor-Precategory algebras-monad-Precategory)
  counit-algebras-monad-Precategory =
    ( λ x →
      ( hom-monad-algebra-Precategory C T x) ,
      ( inv (mul-law-monad-algebra-Precategory C T x))) ,
    ( λ {x} {y} f → eq-pair-Σ
      ( comm-hom-morphism-monad-algebra-Precategory C T x y f)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _)))

  left-triangle-algebras-monad-Precategory :
    has-left-triangle-identity-Precategory C algebras-monad-Precategory
      ( functor-to-algebras-monad-Precategory)
      ( functor-from-algebras-monad-Precategory)
      ( unit-algebras-monad-Precategory)
      ( counit-algebras-monad-Precategory)
  left-triangle-algebras-monad-Precategory x =
    eq-pair-Σ
      ( left-unit-law-mul-hom-family-monad-Precategory C T x)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  right-triangle-algebras-monad-Precategory :
    has-right-triangle-identity-Precategory C algebras-monad-Precategory
      ( functor-to-algebras-monad-Precategory)
      ( functor-from-algebras-monad-Precategory)
      ( unit-algebras-monad-Precategory)
      ( counit-algebras-monad-Precategory)
  right-triangle-algebras-monad-Precategory x =
    unit-law-monad-algebra-Precategory C T x

  adjunction-algebras-monad-Precategory :
    Adjunction-Precategory C algebras-monad-Precategory
  adjunction-algebras-monad-Precategory =
    make-Adjunction-Precategory C algebras-monad-Precategory
      ( functor-to-algebras-monad-Precategory)
      ( functor-from-algebras-monad-Precategory)
      ( is-adjoint-pair-unit-counit-Precategory C algebras-monad-Precategory
        ( functor-to-algebras-monad-Precategory)
        ( functor-from-algebras-monad-Precategory)
        ( unit-algebras-monad-Precategory)
        ( counit-algebras-monad-Precategory)
        ( left-triangle-algebras-monad-Precategory)
        ( right-triangle-algebras-monad-Precategory))
```
