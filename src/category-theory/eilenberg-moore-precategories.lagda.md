# The Eilenberg-Moore precategory

```agda
module category-theory.eilenberg-moore-precategories where
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

The Eilenberg-Moore category `EM(T)` consists of all `T`-algebras and
`T`-algebra morphisms. It comes with an adjunction `C ⇄ EM(T)`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  where

  private
    Tf = endofunctor-monad-Precategory C T
    T₁ = hom-endofunctor-monad-Precategory C T
    T₀ = obj-endofunctor-monad-Precategory C T

  obj-em-monad-Precategory :
    UU (l1 ⊔ l2)
  obj-em-monad-Precategory = monad-algebra-Precategory C T

  hom-set-em-monad-Precategory :
    (a b : obj-em-monad-Precategory) →
    Set l2
  hom-set-em-monad-Precategory a b =
    ( morphism-monad-algebra-Precategory C T a b) ,
    ( is-set-morphism-monad-algebra-Precategory C T a b)

  hom-em-monad-Precategory :
    (a b : obj-em-monad-Precategory) →
    UU l2
  hom-em-monad-Precategory a b =
    type-Set (hom-set-em-monad-Precategory a b)

  comp-hom-em-monad-Precategory :
    (a b c : obj-em-monad-Precategory)
    (g : hom-em-monad-Precategory b c)
    (f : hom-em-monad-Precategory a b) →
    hom-em-monad-Precategory a c
  comp-hom-em-monad-Precategory a b c g f =
    comp-morphism-monad-algebra-Precategory C T a b c g f

  id-hom-em-monad-Precategory :
    (x : obj-em-monad-Precategory) →
    hom-em-monad-Precategory x x
  id-hom-em-monad-Precategory x =
    ( id-hom-Precategory C) ,
    ( left-unit-law-comp-hom-Precategory C
      ( hom-monad-algebra-Precategory C T x)) ∙
    ( inv
      ( right-unit-law-comp-hom-Precategory C
        ( hom-monad-algebra-Precategory C T x))) ∙
    ( ap
      ( postcomp-hom-Precategory C _ _)
      ( inv (preserves-id-endofunctor-monad-Precategory C T _)))

  associative-comp-hom-em-monad-Precategory :
    (x y z w : obj-em-monad-Precategory)
    (h : hom-em-monad-Precategory z w)
    (g : hom-em-monad-Precategory y z)
    (f : hom-em-monad-Precategory x y) →
    (comp-hom-em-monad-Precategory x y w
      ( comp-hom-em-monad-Precategory y z w h g)
      ( f)) ＝
    (comp-hom-em-monad-Precategory x z w
      ( h)
      ( comp-hom-em-monad-Precategory x y z g f))
  associative-comp-hom-em-monad-Precategory x y z w h g f =
    eq-pair-Σ
      ( associative-comp-hom-Precategory C _ _ _)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  left-unit-law-comp-hom-em-monad-Precategory :
    (a b : obj-em-monad-Precategory)
    (f : hom-em-monad-Precategory a b) →
    ( comp-hom-em-monad-Precategory a b b
      ( id-hom-em-monad-Precategory b)
      ( f)) ＝
    ( f)
  left-unit-law-comp-hom-em-monad-Precategory a b f =
    eq-pair-Σ
      ( left-unit-law-comp-hom-Precategory C
        ( hom-morphism-monad-algebra-Precategory C T a b f))
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  right-unit-law-comp-hom-em-monad-Precategory :
    (a b : obj-em-monad-Precategory)
    (f : hom-em-monad-Precategory a b) →
    ( comp-hom-em-monad-Precategory a a b
      ( f)
      ( id-hom-em-monad-Precategory a)) ＝
    ( f)
  right-unit-law-comp-hom-em-monad-Precategory a b f =
    eq-pair-Σ
      ( right-unit-law-comp-hom-Precategory C
        ( hom-morphism-monad-algebra-Precategory C T a b f))
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  em-monad-Precategory : Precategory (l1 ⊔ l2) l2
  em-monad-Precategory =
    make-Precategory
      obj-em-monad-Precategory
      hom-set-em-monad-Precategory
      (λ {a} {b} {c} g f → comp-hom-em-monad-Precategory a b c g f)
      id-hom-em-monad-Precategory
      (λ {a} {b} {c} {d} h g f →
        ( associative-comp-hom-em-monad-Precategory a b c d h g f))
      (λ {a} {b} f → left-unit-law-comp-hom-em-monad-Precategory a b f)
      (λ {a} {b} f → right-unit-law-comp-hom-em-monad-Precategory a b f)

  obj-functor-to-em-monad-Precategory :
    obj-Precategory C → obj-Precategory em-monad-Precategory
  obj-functor-to-em-monad-Precategory x =
    (obj-endofunctor-monad-Precategory C T x) ,
    ((hom-mul-monad-Precategory C T x) ,
      right-unit-law-mul-hom-family-monad-Precategory C T x ,
      associative-mul-hom-family-monad-Precategory C T x)

  hom-functor-to-em-monad-Precategory : {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    hom-Precategory em-monad-Precategory
      (obj-functor-to-em-monad-Precategory x)
      (obj-functor-to-em-monad-Precategory y)
  hom-functor-to-em-monad-Precategory f =
    ( T₁ f) ,
    ( naturality-mul-monad-Precategory C T f)

  preserves-id-functor-to-em-monad-Precategory :
    (x : obj-Precategory C) →
    hom-functor-to-em-monad-Precategory (id-hom-Precategory C {x}) ＝
    id-hom-em-monad-Precategory (obj-functor-to-em-monad-Precategory x)
  preserves-id-functor-to-em-monad-Precategory x =
    eq-pair-Σ
      ( preserves-id-endofunctor-monad-Precategory C T x)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  preserves-comp-functor-to-em-monad-Precategory :
    {x y z : obj-Precategory C} →
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    hom-functor-to-em-monad-Precategory (comp-hom-Precategory C g f) ＝
    comp-hom-em-monad-Precategory
      ( obj-functor-to-em-monad-Precategory x)
      ( obj-functor-to-em-monad-Precategory y)
      ( obj-functor-to-em-monad-Precategory z)
      ( hom-functor-to-em-monad-Precategory g)
      ( hom-functor-to-em-monad-Precategory f)
  preserves-comp-functor-to-em-monad-Precategory g f =
    eq-pair-Σ
      ( preserves-comp-endofunctor-monad-Precategory C T g f)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  functor-to-em-monad-Precategory : functor-Precategory C em-monad-Precategory
  functor-to-em-monad-Precategory =
    obj-functor-to-em-monad-Precategory ,
    hom-functor-to-em-monad-Precategory ,
    preserves-comp-functor-to-em-monad-Precategory ,
    preserves-id-functor-to-em-monad-Precategory

  obj-functor-from-em-monad-Precategory :
    obj-Precategory em-monad-Precategory → obj-Precategory C
  obj-functor-from-em-monad-Precategory = obj-monad-algebra-Precategory C T

  hom-functor-from-em-monad-Precategory :
    (x y : obj-em-monad-Precategory)
    (f : hom-em-monad-Precategory x y) →
    hom-Precategory C
      ( obj-functor-from-em-monad-Precategory x)
      ( obj-functor-from-em-monad-Precategory y)
  hom-functor-from-em-monad-Precategory =
    hom-morphism-monad-algebra-Precategory C T

  preserves-id-functor-from-em-monad-Precategory :
    (x : obj-em-monad-Precategory) →
    hom-functor-from-em-monad-Precategory x x (id-hom-em-monad-Precategory x) ＝
    id-hom-Precategory C
  preserves-id-functor-from-em-monad-Precategory x = refl

  preserves-comp-functor-from-em-monad-Precategory :
    (x y z : obj-em-monad-Precategory)
    (g : hom-em-monad-Precategory y z)
    (f : hom-em-monad-Precategory x y) →
    hom-functor-from-em-monad-Precategory x z
      ( comp-hom-em-monad-Precategory x y z g f) ＝
    comp-hom-Precategory C
      ( hom-functor-from-em-monad-Precategory y z g)
      ( hom-functor-from-em-monad-Precategory x y f)
  preserves-comp-functor-from-em-monad-Precategory x y z g f = refl

  functor-from-em-monad-Precategory : functor-Precategory em-monad-Precategory C
  functor-from-em-monad-Precategory =
    obj-functor-from-em-monad-Precategory ,
    (λ {x} {y} f → hom-functor-from-em-monad-Precategory x y f) ,
    (λ {x} {y} {z} g f →
      preserves-comp-functor-from-em-monad-Precategory x y z g f) ,
    preserves-id-functor-from-em-monad-Precategory
```

The unit of the adjunction between these two functors is exactly the unit of the
monad.

```agda
  unit-em-monad-Precategory :
    natural-transformation-Precategory C C
      (id-functor-Precategory C)
      (comp-functor-Precategory C em-monad-Precategory C
        functor-from-em-monad-Precategory
        functor-to-em-monad-Precategory)
  unit-em-monad-Precategory = unit-monad-Precategory C T
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
  counit-em-monad-Precategory :
    natural-transformation-Precategory em-monad-Precategory em-monad-Precategory
      (comp-functor-Precategory em-monad-Precategory C em-monad-Precategory
        functor-to-em-monad-Precategory functor-from-em-monad-Precategory)
      (id-functor-Precategory em-monad-Precategory)
  counit-em-monad-Precategory =
    (λ x →
      (hom-monad-algebra-Precategory C T x) ,
      inv (mul-law-monad-algebra-Precategory C T x)) ,
    (λ {x} {y} f → eq-pair-Σ
      (comm-hom-morphism-monad-algebra-Precategory C T x y f)
      (eq-is-prop (is-set-hom-Precategory C _ _ _ _)))

  left-triangle-em-monad-Precategory :
    has-left-triangle-identity-Precategory C em-monad-Precategory
      functor-to-em-monad-Precategory
      functor-from-em-monad-Precategory
      unit-em-monad-Precategory
      counit-em-monad-Precategory
  left-triangle-em-monad-Precategory x =
    eq-pair-Σ
      (left-unit-law-mul-hom-family-monad-Precategory C T x)
      (eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  right-triangle-em-monad-Precategory :
    has-right-triangle-identity-Precategory C em-monad-Precategory
      functor-to-em-monad-Precategory
      functor-from-em-monad-Precategory
      unit-em-monad-Precategory
      counit-em-monad-Precategory
  right-triangle-em-monad-Precategory x =
    unit-law-monad-algebra-Precategory C T x

  adjunction-em-monad-Precategory :
    Adjunction-Precategory C em-monad-Precategory
  adjunction-em-monad-Precategory =
    make-Adjunction-Precategory C em-monad-Precategory
      functor-to-em-monad-Precategory
      functor-from-em-monad-Precategory
      (is-adjoint-pair-unit-counit-Precategory C em-monad-Precategory
        functor-to-em-monad-Precategory
        functor-from-em-monad-Precategory
        unit-em-monad-Precategory
        counit-em-monad-Precategory
        left-triangle-em-monad-Precategory
        right-triangle-em-monad-Precategory)
```
