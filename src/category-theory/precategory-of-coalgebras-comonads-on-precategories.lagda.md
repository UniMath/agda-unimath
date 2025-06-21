# The precategory of coalgebras over a comonad

```agda
module category-theory.precategory-of-coalgebras-comonads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-precategories
open import category-theory.coalgebras-comonads-on-precategories
open import category-theory.comonads-on-precategories
open import category-theory.functors-precategories
open import category-theory.morphisms-coalgebras-comonads-on-precategories
open import category-theory.natural-transformations-functors-precategories
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
{{#concept "precategory of coalgebras" Disambiguation="over a comonad on a precategory" Agda=coalgebras-comonad-Precategory}}
over a [comonad on a precategory](category-theory.comonads-on-precategories.md)
`T`, denoted `EM(T)`, also called the **Eilenberg–Moore precategory**, consists
of all `T`-coalgebras and `T`-coalgebra morphisms. It comes with an adjunction
`EM(T) ⇄ C`.

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : comonad-Precategory C)
  where

  obj-coalgebras-comonad-Precategory :
    UU (l1 ⊔ l2)
  obj-coalgebras-comonad-Precategory = coalgebra-comonad-Precategory C T

  hom-set-coalgebras-comonad-Precategory :
    (a b : obj-coalgebras-comonad-Precategory) →
    Set l2
  hom-set-coalgebras-comonad-Precategory a b =
    ( morphism-coalgebra-comonad-Precategory C T a b) ,
    ( is-set-morphism-coalgebra-comonad-Precategory C T a b)

  hom-coalgebras-comonad-Precategory :
    (a b : obj-coalgebras-comonad-Precategory) →
    UU l2
  hom-coalgebras-comonad-Precategory a b =
    type-Set (hom-set-coalgebras-comonad-Precategory a b)

  comp-hom-coalgebras-comonad-Precategory :
    (a b c : obj-coalgebras-comonad-Precategory)
    (g : hom-coalgebras-comonad-Precategory b c)
    (f : hom-coalgebras-comonad-Precategory a b) →
    hom-coalgebras-comonad-Precategory a c
  comp-hom-coalgebras-comonad-Precategory a b c g f =
    comp-morphism-coalgebra-comonad-Precategory C T a b c g f

  coh-id-hom-coalgebras-comonad-Precategory :
    (x : obj-coalgebras-comonad-Precategory) →
    coherence-morphism-coalgebra-comonad-Precategory C T x x
      ( id-hom-Precategory C)
  coh-id-hom-coalgebras-comonad-Precategory x =
    ( ap
      ( precomp-hom-Precategory C _ _)
      ( preserves-id-endofunctor-comonad-Precategory C T _)) ∙
    ( left-unit-law-comp-hom-Precategory C _) ∙
    ( inv
      ( right-unit-law-comp-hom-Precategory C _))

  id-hom-coalgebras-comonad-Precategory :
    (x : obj-coalgebras-comonad-Precategory) →
    hom-coalgebras-comonad-Precategory x x
  id-hom-coalgebras-comonad-Precategory x =
    ( id-hom-Precategory C , coh-id-hom-coalgebras-comonad-Precategory x)

  associative-comp-hom-coalgebras-comonad-Precategory :
    (x y z w : obj-coalgebras-comonad-Precategory)
    (h : hom-coalgebras-comonad-Precategory z w)
    (g : hom-coalgebras-comonad-Precategory y z)
    (f : hom-coalgebras-comonad-Precategory x y) →
    ( comp-hom-coalgebras-comonad-Precategory x y w
      ( comp-hom-coalgebras-comonad-Precategory y z w h g)
      ( f)) ＝
    ( comp-hom-coalgebras-comonad-Precategory x z w
      ( h)
      ( comp-hom-coalgebras-comonad-Precategory x y z g f))
  associative-comp-hom-coalgebras-comonad-Precategory x y z w h g f =
    eq-pair-Σ
      ( associative-comp-hom-Precategory C _ _ _)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  left-counit-law-comp-hom-coalgebras-comonad-Precategory :
    (a b : obj-coalgebras-comonad-Precategory)
    (f : hom-coalgebras-comonad-Precategory a b) →
    ( comp-hom-coalgebras-comonad-Precategory a b b
      ( id-hom-coalgebras-comonad-Precategory b)
      ( f)) ＝
    ( f)
  left-counit-law-comp-hom-coalgebras-comonad-Precategory a b f =
    eq-pair-Σ
      ( left-unit-law-comp-hom-Precategory C
        ( hom-morphism-coalgebra-comonad-Precategory C T a b f))
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  right-counit-law-comp-hom-coalgebras-comonad-Precategory :
    (a b : obj-coalgebras-comonad-Precategory)
    (f : hom-coalgebras-comonad-Precategory a b) →
    ( comp-hom-coalgebras-comonad-Precategory a a b
      ( f)
      ( id-hom-coalgebras-comonad-Precategory a)) ＝
    ( f)
  right-counit-law-comp-hom-coalgebras-comonad-Precategory a b f =
    eq-pair-Σ
      ( right-unit-law-comp-hom-Precategory C
        ( hom-morphism-coalgebra-comonad-Precategory C T a b f))
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  coalgebras-comonad-Precategory : Precategory (l1 ⊔ l2) l2
  coalgebras-comonad-Precategory =
    make-Precategory
      ( obj-coalgebras-comonad-Precategory)
      ( hom-set-coalgebras-comonad-Precategory)
      ( λ {a} {b} {c} g f → comp-hom-coalgebras-comonad-Precategory a b c g f)
      ( id-hom-coalgebras-comonad-Precategory)
      ( λ {a} {b} {c} {d} h g f →
        ( associative-comp-hom-coalgebras-comonad-Precategory a b c d h g f))
      ( λ {a} {b} f →
        left-counit-law-comp-hom-coalgebras-comonad-Precategory a b f)
      ( λ {a} {b} f →
        right-counit-law-comp-hom-coalgebras-comonad-Precategory a b f)
```

## Properties

### Free functor from the underlying category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : comonad-Precategory C)
  (let T₁ = hom-endofunctor-comonad-Precategory C T)
  where

  obj-functor-to-coalgebras-comonad-Precategory :
    obj-Precategory C → obj-Precategory (coalgebras-comonad-Precategory C T)
  obj-functor-to-coalgebras-comonad-Precategory x =
    ( obj-endofunctor-comonad-Precategory C T x) ,
    ( ( hom-comul-comonad-Precategory C T x) ,
      ( right-counit-law-comul-hom-family-comonad-Precategory C T x) ,
      ( associative-comul-hom-family-comonad-Precategory C T x))

  hom-functor-to-coalgebras-comonad-Precategory :
    {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    hom-Precategory (coalgebras-comonad-Precategory C T)
      ( obj-functor-to-coalgebras-comonad-Precategory x)
      ( obj-functor-to-coalgebras-comonad-Precategory y)
  hom-functor-to-coalgebras-comonad-Precategory f =
    ( T₁ f) ,
    ( naturality-comul-comonad-Precategory C T f)

  preserves-id-functor-to-coalgebras-comonad-Precategory :
    (x : obj-Precategory C) →
    hom-functor-to-coalgebras-comonad-Precategory (id-hom-Precategory C {x}) ＝
    id-hom-coalgebras-comonad-Precategory C T
      ( obj-functor-to-coalgebras-comonad-Precategory x)
  preserves-id-functor-to-coalgebras-comonad-Precategory x =
    eq-pair-Σ
      ( preserves-id-endofunctor-comonad-Precategory C T x)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  preserves-comp-functor-to-coalgebras-comonad-Precategory :
    {x y z : obj-Precategory C} →
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    hom-functor-to-coalgebras-comonad-Precategory (comp-hom-Precategory C g f) ＝
    comp-hom-coalgebras-comonad-Precategory C T
      ( obj-functor-to-coalgebras-comonad-Precategory x)
      ( obj-functor-to-coalgebras-comonad-Precategory y)
      ( obj-functor-to-coalgebras-comonad-Precategory z)
      ( hom-functor-to-coalgebras-comonad-Precategory g)
      ( hom-functor-to-coalgebras-comonad-Precategory f)
  preserves-comp-functor-to-coalgebras-comonad-Precategory g f =
    eq-pair-Σ
      ( preserves-comp-endofunctor-comonad-Precategory C T g f)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  functor-to-coalgebras-comonad-Precategory :
    functor-Precategory C (coalgebras-comonad-Precategory C T)
  functor-to-coalgebras-comonad-Precategory =
    ( obj-functor-to-coalgebras-comonad-Precategory) ,
    ( hom-functor-to-coalgebras-comonad-Precategory) ,
    ( preserves-comp-functor-to-coalgebras-comonad-Precategory) ,
    ( preserves-id-functor-to-coalgebras-comonad-Precategory)
```

### Forgetful functor from the underlying precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : comonad-Precategory C)
  where

  obj-functor-from-coalgebras-comonad-Precategory :
    obj-coalgebras-comonad-Precategory C T → obj-Precategory C
  obj-functor-from-coalgebras-comonad-Precategory =
    obj-coalgebra-comonad-Precategory C T

  hom-functor-from-coalgebras-comonad-Precategory :
    (x y : obj-coalgebras-comonad-Precategory C T)
    (f : hom-coalgebras-comonad-Precategory C T x y) →
    hom-Precategory C
      ( obj-functor-from-coalgebras-comonad-Precategory x)
      ( obj-functor-from-coalgebras-comonad-Precategory y)
  hom-functor-from-coalgebras-comonad-Precategory =
    hom-morphism-coalgebra-comonad-Precategory C T

  preserves-id-functor-from-coalgebras-comonad-Precategory :
    (x : obj-coalgebras-comonad-Precategory C T) →
    hom-functor-from-coalgebras-comonad-Precategory x x
      ( id-hom-coalgebras-comonad-Precategory C T x) ＝
    id-hom-Precategory C
  preserves-id-functor-from-coalgebras-comonad-Precategory x = refl

  preserves-comp-functor-from-coalgebras-comonad-Precategory :
    (x y z : obj-coalgebras-comonad-Precategory C T)
    (g : hom-coalgebras-comonad-Precategory C T y z)
    (f : hom-coalgebras-comonad-Precategory C T x y) →
    hom-functor-from-coalgebras-comonad-Precategory x z
      ( comp-hom-coalgebras-comonad-Precategory C T x y z g f) ＝
    comp-hom-Precategory C
      ( hom-functor-from-coalgebras-comonad-Precategory y z g)
      ( hom-functor-from-coalgebras-comonad-Precategory x y f)
  preserves-comp-functor-from-coalgebras-comonad-Precategory x y z g f = refl

  functor-from-coalgebras-comonad-Precategory :
    functor-Precategory (coalgebras-comonad-Precategory C T) C
  functor-from-coalgebras-comonad-Precategory =
    ( obj-functor-from-coalgebras-comonad-Precategory) ,
    ( λ {x} {y} f → hom-functor-from-coalgebras-comonad-Precategory x y f) ,
    ( λ {x} {y} {z} g f →
      preserves-comp-functor-from-coalgebras-comonad-Precategory x y z g f) ,
    ( preserves-id-functor-from-coalgebras-comonad-Precategory)
```

### Adjunction with the underlying category

The counit of the adjunction between these two functors is exactly the counit of
the comonad.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : comonad-Precategory C)
  where

  counit-coalgebras-comonad-Precategory :
    natural-transformation-Precategory C C
      ( comp-functor-Precategory C (coalgebras-comonad-Precategory C T) C
        ( functor-from-coalgebras-comonad-Precategory C T)
        ( functor-to-coalgebras-comonad-Precategory C T))
      ( id-functor-Precategory C)
  counit-coalgebras-comonad-Precategory = counit-comonad-Precategory C T
```

The unit is the horizontal map given by the structure map of the coalgebra

```text
        a
    x -----> Tx
    |         |
  a |         | δ
    ∨         ∨
   Tx -----> T²x.
        Ta
```

```agda
  unit-coalgebras-comonad-Precategory :
    natural-transformation-Precategory
      ( coalgebras-comonad-Precategory C T)
      ( coalgebras-comonad-Precategory C T)
      ( id-functor-Precategory (coalgebras-comonad-Precategory C T))
      ( comp-functor-Precategory
        ( coalgebras-comonad-Precategory C T)
        ( C)
        ( coalgebras-comonad-Precategory C T)
        ( functor-to-coalgebras-comonad-Precategory C T)
        ( functor-from-coalgebras-comonad-Precategory C T))
  unit-coalgebras-comonad-Precategory =
    ( λ x →
      ( hom-coalgebra-comonad-Precategory C T x) ,
      ( comul-law-coalgebra-comonad-Precategory C T x)) ,
    ( λ {x} {y} f →
      eq-pair-Σ
        ( coh-hom-morphism-coalgebra-comonad-Precategory C T x y f)
        ( eq-is-prop (is-set-hom-Precategory C _ _ _ _)))

  right-triangle-coalgebras-comonad-Precategory :
    has-right-triangle-identity-Precategory
      ( coalgebras-comonad-Precategory C T)
      ( C)
      ( functor-from-coalgebras-comonad-Precategory C T)
      ( functor-to-coalgebras-comonad-Precategory C T)
      ( unit-coalgebras-comonad-Precategory)
      ( counit-coalgebras-comonad-Precategory)
  right-triangle-coalgebras-comonad-Precategory x =
    eq-pair-Σ
      ( left-counit-law-comul-hom-family-comonad-Precategory C T x)
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  left-triangle-coalgebras-comonad-Precategory :
    has-left-triangle-identity-Precategory
      ( coalgebras-comonad-Precategory C T)
      ( C)
      ( functor-from-coalgebras-comonad-Precategory C T)
      ( functor-to-coalgebras-comonad-Precategory C T)
      ( unit-coalgebras-comonad-Precategory)
      ( counit-coalgebras-comonad-Precategory)
  left-triangle-coalgebras-comonad-Precategory x =
    counit-law-coalgebra-comonad-Precategory C T x

  adjunction-coalgebras-comonad-Precategory :
    Adjunction-Precategory (coalgebras-comonad-Precategory C T) C
  adjunction-coalgebras-comonad-Precategory =
    make-Adjunction-Precategory (coalgebras-comonad-Precategory C T) C
      ( functor-from-coalgebras-comonad-Precategory C T)
      ( functor-to-coalgebras-comonad-Precategory C T)
      ( is-adjoint-pair-unit-counit-Precategory
        ( coalgebras-comonad-Precategory C T)
        ( C)
        ( functor-from-coalgebras-comonad-Precategory C T)
        ( functor-to-coalgebras-comonad-Precategory C T)
        ( unit-coalgebras-comonad-Precategory)
        ( counit-coalgebras-comonad-Precategory)
        ( left-triangle-coalgebras-comonad-Precategory)
        ( right-triangle-coalgebras-comonad-Precategory))
```
