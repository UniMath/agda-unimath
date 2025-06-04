# Algebras over monads on precategories

```agda
module category-theory.algebras-monads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategories
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
```

</details>

## Idea

An
{{#concept "algebra over a monad" Disambiguation="on a precategory" Agda=algebra-monad-Precategory}}
over a [monad](category-theory.monads-on-precategories.md) `T` consists of an
object `A` and morphism `a : TA → A` satisfying two compatibility laws:

- **Unit law**: `a ∘ η_A = id_A`
- **Multiplication law**: `a ∘ Ta = a ∘ μ_A`

## Definitions

### Algebras over a monad

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  where

  module _
    {A : obj-Precategory C}
    (a : hom-Precategory C (obj-endofunctor-monad-Precategory C T A) A)
    where

    has-unit-law-algebra-monad-Precategory : UU l2
    has-unit-law-algebra-monad-Precategory =
      comp-hom-Precategory C a (hom-unit-monad-Precategory C T A) ＝
      id-hom-Precategory C

    has-mul-law-algebra-monad-Precategory : UU l2
    has-mul-law-algebra-monad-Precategory =
      comp-hom-Precategory C a (hom-endofunctor-monad-Precategory C T a) ＝
      comp-hom-Precategory C a (hom-mul-monad-Precategory C T A)

    is-algebra-monad-Precategory : UU l2
    is-algebra-monad-Precategory =
      has-unit-law-algebra-monad-Precategory ×
      has-mul-law-algebra-monad-Precategory

  algebra-monad-Precategory : UU (l1 ⊔ l2)
  algebra-monad-Precategory =
    Σ ( obj-Precategory C)
      ( λ A →
        Σ ( hom-Precategory C (obj-endofunctor-monad-Precategory C T A) A)
          ( λ a → is-algebra-monad-Precategory a))

  obj-algebra-monad-Precategory : algebra-monad-Precategory → obj-Precategory C
  obj-algebra-monad-Precategory = pr1

  hom-algebra-monad-Precategory :
    (f : algebra-monad-Precategory) →
    hom-Precategory C
      ( obj-endofunctor-monad-Precategory C T (obj-algebra-monad-Precategory f))
      ( obj-algebra-monad-Precategory f)
  hom-algebra-monad-Precategory f = pr1 (pr2 f)

  comm-algebra-monad-Precategory :
    (f : algebra-monad-Precategory) →
    is-algebra-monad-Precategory (hom-algebra-monad-Precategory f)
  comm-algebra-monad-Precategory f = pr2 (pr2 f)

  unit-law-algebra-monad-Precategory :
    (f : algebra-monad-Precategory) →
    has-unit-law-algebra-monad-Precategory (hom-algebra-monad-Precategory f)
  unit-law-algebra-monad-Precategory f = pr1 (pr2 (pr2 f))

  mul-law-algebra-monad-Precategory :
    (f : algebra-monad-Precategory) →
    has-mul-law-algebra-monad-Precategory (hom-algebra-monad-Precategory f)
  mul-law-algebra-monad-Precategory f = pr2 (pr2 (pr2 f))

  morphism-algebra-monad-Precategory : (f g : algebra-monad-Precategory) → UU l2
  morphism-algebra-monad-Precategory f g =
    Σ ( hom-Precategory C
        ( obj-algebra-monad-Precategory f)
        ( obj-algebra-monad-Precategory g))
      ( λ h →
        coherence-square-hom-Precategory C
          ( hom-endofunctor-monad-Precategory C T h)
          ( hom-algebra-monad-Precategory f)
          ( hom-algebra-monad-Precategory g)
          ( h))

  hom-morphism-algebra-monad-Precategory :
    (f g : algebra-monad-Precategory)
    (h : morphism-algebra-monad-Precategory f g) →
    hom-Precategory C
      ( obj-algebra-monad-Precategory f)
      ( obj-algebra-monad-Precategory g)
  hom-morphism-algebra-monad-Precategory f g h = pr1 h

  top-hom-morphism-algebra-monad-Precategory :
    (f g : algebra-monad-Precategory)
    (h : morphism-algebra-monad-Precategory f g) →
    hom-Precategory C
      ( obj-endofunctor-monad-Precategory C T (obj-algebra-monad-Precategory f))
      ( obj-endofunctor-monad-Precategory C T (obj-algebra-monad-Precategory g))
  top-hom-morphism-algebra-monad-Precategory f g h =
    hom-endofunctor-monad-Precategory C T
      ( hom-morphism-algebra-monad-Precategory f g h)

  comm-hom-morphism-algebra-monad-Precategory :
    (f g : algebra-monad-Precategory)
    (h : morphism-algebra-monad-Precategory f g) →
    coherence-square-hom-Precategory C
      ( top-hom-morphism-algebra-monad-Precategory f g h)
      ( hom-algebra-monad-Precategory f)
      ( hom-algebra-monad-Precategory g)
      ( hom-morphism-algebra-monad-Precategory f g h)
  comm-hom-morphism-algebra-monad-Precategory f g h = pr2 h

  comp-morphism-algebra-monad-Precategory :
    (a b c : algebra-monad-Precategory)
    (g : morphism-algebra-monad-Precategory b c) →
    (f : morphism-algebra-monad-Precategory a b) →
    morphism-algebra-monad-Precategory a c
  comp-morphism-algebra-monad-Precategory a b c g f =
    ( comp-hom-Precategory C
      ( hom-morphism-algebra-monad-Precategory b c g)
      ( hom-morphism-algebra-monad-Precategory a b f)) ,
    ( pasting-horizontal-coherence-square-hom-Precategory C
      ( top-hom-morphism-algebra-monad-Precategory a b f)
      ( top-hom-morphism-algebra-monad-Precategory b c g)
      ( hom-algebra-monad-Precategory a)
      ( hom-algebra-monad-Precategory b)
      ( hom-algebra-monad-Precategory c)
      ( hom-morphism-algebra-monad-Precategory a b f)
      ( hom-morphism-algebra-monad-Precategory b c g)
      ( comm-hom-morphism-algebra-monad-Precategory a b f)
      ( comm-hom-morphism-algebra-monad-Precategory b c g)) ∙
    ( ap
      ( postcomp-hom-Precategory C (hom-algebra-monad-Precategory c) _)
      ( inv (preserves-comp-endofunctor-monad-Precategory C T _ _)))

  is-set-morphism-algebra-monad-Precategory :
    (f g : algebra-monad-Precategory) →
    is-set (morphism-algebra-monad-Precategory f g)
  is-set-morphism-algebra-monad-Precategory f g =
    is-set-Σ
      ( is-set-hom-Precategory C _ _)
      ( λ hk → is-set-is-prop (is-set-hom-Precategory C _ _ _ _))
```
