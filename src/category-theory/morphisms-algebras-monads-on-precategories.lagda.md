# Morphisms of algebras over monads on precategories

```agda
module category-theory.morphisms-algebras-monads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.algebras-monads-on-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.monads-on-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of monad algebras on a precategory" Agda=algebra-monad-Precategory}}
between [monad algebras](category-theory.algebras-monads-on-precategories.md)
`a : TA → A` and `b : TB → B` is a map `f : A → B` such that `b ∘ Tf = f ∘ a`.

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  where

  coherence-morphism-algebra-monad-Precategory :
    (f g : algebra-monad-Precategory C T) →
    hom-Precategory C
      ( obj-algebra-monad-Precategory C T f)
      ( obj-algebra-monad-Precategory C T g) →
    UU l2
  coherence-morphism-algebra-monad-Precategory f g h =
    coherence-square-hom-Precategory C
      ( hom-endofunctor-monad-Precategory C T h)
      ( hom-algebra-monad-Precategory C T f)
      ( hom-algebra-monad-Precategory C T g)
      ( h)

  morphism-algebra-monad-Precategory :
    (f g : algebra-monad-Precategory C T) → UU l2
  morphism-algebra-monad-Precategory f g =
    Σ ( hom-Precategory C
        ( obj-algebra-monad-Precategory C T f)
        ( obj-algebra-monad-Precategory C T g))
      ( coherence-morphism-algebra-monad-Precategory f g)

  hom-morphism-algebra-monad-Precategory :
    (f g : algebra-monad-Precategory C T)
    (h : morphism-algebra-monad-Precategory f g) →
    hom-Precategory C
      ( obj-algebra-monad-Precategory C T f)
      ( obj-algebra-monad-Precategory C T g)
  hom-morphism-algebra-monad-Precategory f g h = pr1 h

  top-hom-morphism-algebra-monad-Precategory :
    (f g : algebra-monad-Precategory C T)
    (h : morphism-algebra-monad-Precategory f g) →
    hom-Precategory C
      ( obj-endofunctor-monad-Precategory C T
        ( obj-algebra-monad-Precategory C T f))
      ( obj-endofunctor-monad-Precategory C T
        ( obj-algebra-monad-Precategory C T g))
  top-hom-morphism-algebra-monad-Precategory f g h =
    hom-endofunctor-monad-Precategory C T
      ( hom-morphism-algebra-monad-Precategory f g h)

  coh-hom-morphism-algebra-monad-Precategory :
    (f g : algebra-monad-Precategory C T)
    (h : morphism-algebra-monad-Precategory f g) →
    coherence-square-hom-Precategory C
      ( top-hom-morphism-algebra-monad-Precategory f g h)
      ( hom-algebra-monad-Precategory C T f)
      ( hom-algebra-monad-Precategory C T g)
      ( hom-morphism-algebra-monad-Precategory f g h)
  coh-hom-morphism-algebra-monad-Precategory f g h = pr2 h

  comp-morphism-algebra-monad-Precategory :
    (a b c : algebra-monad-Precategory C T)
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
      ( hom-algebra-monad-Precategory C T a)
      ( hom-algebra-monad-Precategory C T b)
      ( hom-algebra-monad-Precategory C T c)
      ( hom-morphism-algebra-monad-Precategory a b f)
      ( hom-morphism-algebra-monad-Precategory b c g)
      ( coh-hom-morphism-algebra-monad-Precategory a b f)
      ( coh-hom-morphism-algebra-monad-Precategory b c g)) ∙
    ( ap
      ( postcomp-hom-Precategory C (hom-algebra-monad-Precategory C T c) _)
      ( inv (preserves-comp-endofunctor-monad-Precategory C T _ _)))

  is-set-morphism-algebra-monad-Precategory :
    (f g : algebra-monad-Precategory C T) →
    is-set (morphism-algebra-monad-Precategory f g)
  is-set-morphism-algebra-monad-Precategory f g =
    is-set-Σ
      ( is-set-hom-Precategory C _ _)
      ( λ hk → is-set-is-prop (is-set-hom-Precategory C _ _ _ _))
```
