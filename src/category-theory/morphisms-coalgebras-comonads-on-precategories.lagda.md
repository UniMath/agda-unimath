# Morphisms of coalgebras over comonads on precategories

```agda
module category-theory.morphisms-coalgebras-comonads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.coalgebras-comonads-on-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.comonads-on-precategories
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
{{#concept "morphism" Disambiguation="of comonad coalgebras on a precategory" Agda=coalgebra-comonad-Precategory}}
between
[comonad coalgebras](category-theory.coalgebras-comonads-on-precategories.md)
`a : A → TA` and `b : B → TB` is a map `f : A → B` such that `Tf ∘ b = a ∘ f`.

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : comonad-Precategory C)
  where

  coherence-morphism-coalgebra-comonad-Precategory :
    (f g : coalgebra-comonad-Precategory C T) →
    hom-Precategory C
      ( obj-coalgebra-comonad-Precategory C T f)
      ( obj-coalgebra-comonad-Precategory C T g) →
    UU l2
  coherence-morphism-coalgebra-comonad-Precategory f g h =
    coherence-square-hom-Precategory C
      ( h)
      ( hom-coalgebra-comonad-Precategory C T f)
      ( hom-coalgebra-comonad-Precategory C T g)
      ( hom-endofunctor-comonad-Precategory C T h)

  morphism-coalgebra-comonad-Precategory :
    (f g : coalgebra-comonad-Precategory C T) → UU l2
  morphism-coalgebra-comonad-Precategory f g =
    Σ ( hom-Precategory C
        ( obj-coalgebra-comonad-Precategory C T f)
        ( obj-coalgebra-comonad-Precategory C T g))
      ( coherence-morphism-coalgebra-comonad-Precategory f g)

  hom-morphism-coalgebra-comonad-Precategory :
    (f g : coalgebra-comonad-Precategory C T)
    (h : morphism-coalgebra-comonad-Precategory f g) →
    hom-Precategory C
      ( obj-coalgebra-comonad-Precategory C T f)
      ( obj-coalgebra-comonad-Precategory C T g)
  hom-morphism-coalgebra-comonad-Precategory f g h = pr1 h

  bottom-hom-morphism-coalgebra-comonad-Precategory :
    (f g : coalgebra-comonad-Precategory C T)
    (h : morphism-coalgebra-comonad-Precategory f g) →
    hom-Precategory C
      ( obj-endofunctor-comonad-Precategory C T
        ( obj-coalgebra-comonad-Precategory C T f))
      ( obj-endofunctor-comonad-Precategory C T
        ( obj-coalgebra-comonad-Precategory C T g))
  bottom-hom-morphism-coalgebra-comonad-Precategory f g h =
    hom-endofunctor-comonad-Precategory C T
      ( hom-morphism-coalgebra-comonad-Precategory f g h)

  coh-hom-morphism-coalgebra-comonad-Precategory :
    (f g : coalgebra-comonad-Precategory C T)
    (h : morphism-coalgebra-comonad-Precategory f g) →
    coherence-square-hom-Precategory C
      ( hom-morphism-coalgebra-comonad-Precategory f g h)
      ( hom-coalgebra-comonad-Precategory C T f)
      ( hom-coalgebra-comonad-Precategory C T g)
      ( bottom-hom-morphism-coalgebra-comonad-Precategory f g h)
  coh-hom-morphism-coalgebra-comonad-Precategory f g h = pr2 h

  comp-morphism-coalgebra-comonad-Precategory :
    (a b c : coalgebra-comonad-Precategory C T)
    (g : morphism-coalgebra-comonad-Precategory b c) →
    (f : morphism-coalgebra-comonad-Precategory a b) →
    morphism-coalgebra-comonad-Precategory a c
  comp-morphism-coalgebra-comonad-Precategory a b c g f =
    ( comp-hom-Precategory C
      ( hom-morphism-coalgebra-comonad-Precategory b c g)
      ( hom-morphism-coalgebra-comonad-Precategory a b f)) ,
    ( ap
      ( precomp-hom-Precategory C (hom-coalgebra-comonad-Precategory C T a) _)
      ( preserves-comp-endofunctor-comonad-Precategory C T _ _)) ∙
    ( pasting-horizontal-coherence-square-hom-Precategory C
      ( hom-morphism-coalgebra-comonad-Precategory a b f)
      ( hom-morphism-coalgebra-comonad-Precategory b c g)
      ( hom-coalgebra-comonad-Precategory C T a)
      ( hom-coalgebra-comonad-Precategory C T b)
      ( hom-coalgebra-comonad-Precategory C T c)
      ( bottom-hom-morphism-coalgebra-comonad-Precategory a b f)
      ( bottom-hom-morphism-coalgebra-comonad-Precategory b c g)
      ( coh-hom-morphism-coalgebra-comonad-Precategory a b f)
      ( coh-hom-morphism-coalgebra-comonad-Precategory b c g))

  is-set-morphism-coalgebra-comonad-Precategory :
    (f g : coalgebra-comonad-Precategory C T) →
    is-set (morphism-coalgebra-comonad-Precategory f g)
  is-set-morphism-coalgebra-comonad-Precategory f g =
    is-set-Σ
      ( is-set-hom-Precategory C _ _)
      ( λ hk → is-set-is-prop (is-set-hom-Precategory C _ _ _ _))
```
