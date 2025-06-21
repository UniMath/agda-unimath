# Density comonads on precategories

```agda
module category-theory.density-comonads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.coalgebras-comonads-on-precategories
open import category-theory.comonads-on-precategories
open import category-theory.functors-precategories
open import category-theory.left-extensions-precategories
open import category-theory.left-kan-extensions-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given an arbitrary [functor](category-theory.functors-precategories.md)
`F : C → D`, any [left Kan
extension](category-theory.left-kan-extensions-precategories.md] `L` of `F`
along itself has a canonical
[comonad](category-theory.comonads-on-precategories.md) structure, called the
{{#concept "density comonad" Agda=density-comonad-Precategory}} of `L`.

## Comonad structure

The counit and comultiplication of the density comonads follow from the
"existence" part of the universal property of the right Kan extension. We use
two right extensions: the identity map on `D` trivially gives a right extension
of `D` along itself, and `L²` gives an extension by whiskering and composing the
natural transformation. By the universal property of `L`, these give natural
transformations `η : id ⇒ L` and `μ : L² ⇒ L`, respectively. From their
definition via the universal property, we have two computation rules for these
natural transformations (where ∙ is whiskering):

1. `α ∘ (η ∙ F) ＝ id_F`; and
2. `α ∘ (μ ∙ F) ＝ α ∘ (L ∙ α)`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Lk : left-kan-extension-Precategory C D D F F)
  (let L = extension-left-kan-extension-Precategory C D D F F Lk)
  (let KL = is-left-kan-extension-left-kan-extension-Precategory C D D F F Lk)
  (let α = natural-transformation-left-kan-extension-Precategory C D D F F Lk)
  (let LL = comp-functor-Precategory D D D L L)
  (let LF = comp-functor-Precategory C D D L F)
  (let LLF = comp-functor-Precategory C D D LL F)
  where

  counit-density-comonad-Precategory :
    natural-transformation-Precategory D D L (id-functor-Precategory D)
  counit-density-comonad-Precategory =
    map-inv-is-equiv
      ( KL (id-functor-Precategory D))
      ( pr2 (id-left-extension-Precategory C D F))

  abstract
    compute-counit-density-comonad-Precategory :
      comp-natural-transformation-Precategory C D F LF F
        ( right-whisker-natural-transformation-Precategory D D C
          ( L)
          ( id-functor-Precategory D)
          ( counit-density-comonad-Precategory)
          ( F))
        ( α) ＝
      id-natural-transformation-Precategory C D F
    compute-counit-density-comonad-Precategory =
      is-section-map-inv-is-equiv (KL _) _

  comul-density-comonad-Precategory :
    natural-transformation-Precategory D D
      ( L)
      ( comp-functor-Precategory D D D L L)
  comul-density-comonad-Precategory =
    map-inv-is-equiv
      ( KL (comp-functor-Precategory D D D L L))
      ( pr2
        ( square-left-extension-Precategory C D F
          ( left-extension-left-kan-extension-Precategory C D D F F Lk)))

  abstract
    compute-comul-density-comonad-Precategory :
      comp-natural-transformation-Precategory C D F LF LLF
        ( right-whisker-natural-transformation-Precategory D D C
          ( L)
          ( LL)
          ( comul-density-comonad-Precategory)
          ( F))
        ( α) ＝
      comp-natural-transformation-Precategory C D F LF LLF
        ( left-whisker-natural-transformation-Precategory C D D
          ( F)
          ( LF)
          ( L)
          ( α))
        ( α)
    compute-comul-density-comonad-Precategory =
      is-section-map-inv-is-equiv (KL _) _
```

## Comonad laws

Comonad laws follow from the "uniqueness" part of the right Kan extension. See
[codensity monads](category-theory.codensity-monads-on-precategories.md) for an
explanation of the (dual) proofs.

### Left counit law

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Lk : left-kan-extension-Precategory C D D F F)
  (let L = extension-left-kan-extension-Precategory C D D F F Lk)
  (let KL = is-left-kan-extension-left-kan-extension-Precategory C D D F F Lk)
  (let α = natural-transformation-left-kan-extension-Precategory C D D F F Lk)
  (let LL = comp-functor-Precategory D D D L L)
  (let LF = comp-functor-Precategory C D D L F)
  (let LLF = comp-functor-Precategory C D D LL F)
  where

  precomp-left-counit-law-comul-density-comonad-Precategory :
    left-extension-map-Precategory C D D F F (L , α) L
      ( comp-natural-transformation-Precategory
        D D L LL L
        ( left-whisker-natural-transformation-Precategory D D D
          ( L)
          ( id-functor-Precategory D)
          ( L)
          ( counit-density-comonad-Precategory C D F Lk))
        ( comul-density-comonad-Precategory C D F Lk)) ＝
    α
  precomp-left-counit-law-comul-density-comonad-Precategory =
    ( associative-comp-natural-transformation-Precategory C D F LF LLF LF
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( λ x →
        comp-natural-transformation-Precategory C D F LLF LF
          ( right-whisker-natural-transformation-Precategory D D C LL L
            ( left-whisker-natural-transformation-Precategory D D D
              ( L)
              ( id-functor-Precategory D)
              ( L)
              ( counit-density-comonad-Precategory C D F Lk))
            ( F))
          ( x))
      ( compute-comul-density-comonad-Precategory C D F Lk)) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D F LF LLF LF
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D F LF LF
          ( x)
          ( α)))
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory
          ( C)
          ( D)
          ( D)
          ( F)
          ( LF)
          ( F)
          ( L)
          ( right-whisker-natural-transformation-Precategory D D C
            ( L)
            ( id-functor-Precategory D)
            ( counit-density-comonad-Precategory C D F Lk)
            ( F))
          ( α)))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D F LF LF
          ( left-whisker-natural-transformation-Precategory C D D F F
            ( L)
            ( x))
          ( α)))
      ( compute-counit-density-comonad-Precategory C D F Lk)) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D F LF LF
          ( x)
          ( α)))
      ( preserves-id-left-whisker-natural-transformation-Precategory C D D
        ( F)
        ( L))) ∙
    ( left-unit-law-comp-natural-transformation-Precategory C D F LF α)

  abstract
    left-counit-law-comul-density-comonad-Precategory :
      comp-natural-transformation-Precategory
        D D L (comp-functor-Precategory D D D L L) L
        ( left-whisker-natural-transformation-Precategory D D D
          ( L)
          ( id-functor-Precategory D)
          ( L)
          ( counit-density-comonad-Precategory C D F Lk))
        ( comul-density-comonad-Precategory C D F Lk) ＝
      id-natural-transformation-Precategory D D L
    left-counit-law-comul-density-comonad-Precategory =
      ( inv (is-retraction-map-inv-is-equiv (KL L) _)) ∙
      ( ap
        ( map-inv-is-equiv (KL L))
        ( ( precomp-left-counit-law-comul-density-comonad-Precategory) ∙
          ( inv
            ( left-unit-law-comp-natural-transformation-Precategory C D
              ( F)
              ( LF)
              ( α))))) ∙
      ( is-retraction-map-inv-is-equiv (KL L) _)
```

### Right counit law

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Lk : left-kan-extension-Precategory C D D F F)
  (let L = extension-left-kan-extension-Precategory C D D F F Lk)
  (let KL = is-left-kan-extension-left-kan-extension-Precategory C D D F F Lk)
  (let α = natural-transformation-left-kan-extension-Precategory C D D F F Lk)
  (let LL = comp-functor-Precategory D D D L L)
  (let LF = comp-functor-Precategory C D D L F)
  (let LLF = comp-functor-Precategory C D D LL F)
  where

  precomp-right-counit-law-comul-density-comonad-Precategory :
    left-extension-map-Precategory C D D F F (L , α) L
      ( comp-natural-transformation-Precategory
        D D L LL L
        ( right-whisker-natural-transformation-Precategory D D D
          ( L)
          ( id-functor-Precategory D)
          ( counit-density-comonad-Precategory C D F Lk)
          ( L))
        ( comul-density-comonad-Precategory C D F Lk)) ＝
    α
  precomp-right-counit-law-comul-density-comonad-Precategory =
    ( associative-comp-natural-transformation-Precategory C D F LF LLF LF
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( comp-natural-transformation-Precategory C D F LLF LF
        ( right-whisker-natural-transformation-Precategory D D C LL L
          ( right-whisker-natural-transformation-Precategory D D D
            ( L)
            ( id-functor-Precategory D)
            ( counit-density-comonad-Precategory C D F Lk)
            ( L))
          ( F)))
      ( is-section-map-inv-is-equiv
        ( KL (comp-functor-Precategory D D D L L)) _)) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D F LF LLF LF
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D F LF LF x α)
      ( eq-htpy-hom-family-natural-transformation-Precategory C D LF LF _ _
        (λ x →
          inv
            ( naturality-natural-transformation-Precategory D D
              ( L)
              ( id-functor-Precategory D)
              ( counit-density-comonad-Precategory C D F Lk)
              ( _))))) ∙
    ( associative-comp-natural-transformation-Precategory C D F LF F LF
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( comp-natural-transformation-Precategory C D F F LF α)
      ( compute-counit-density-comonad-Precategory C D F Lk)) ∙
    right-unit-law-comp-natural-transformation-Precategory C D F LF α

  abstract
    right-counit-law-comul-density-comonad-Precategory :
      comp-natural-transformation-Precategory
        D D L (comp-functor-Precategory D D D L L) L
        ( right-whisker-natural-transformation-Precategory D D D
          ( L)
          ( id-functor-Precategory D)
          ( counit-density-comonad-Precategory C D F Lk)
          ( L))
        ( comul-density-comonad-Precategory C D F Lk) ＝
      id-natural-transformation-Precategory D D L
    right-counit-law-comul-density-comonad-Precategory =
      ( inv (is-retraction-map-inv-is-equiv (KL L) _)) ∙
      ( ap
        ( map-inv-is-equiv (KL L))
        ( ( precomp-right-counit-law-comul-density-comonad-Precategory) ∙
          ( inv
            ( left-unit-law-comp-natural-transformation-Precategory C D
              ( F)
              ( LF)
              ( α))))) ∙
      ( is-retraction-map-inv-is-equiv (KL L) _)
```

### Comultiplication is associative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Lk : left-kan-extension-Precategory C D D F F)
  (let L = extension-left-kan-extension-Precategory C D D F F Lk)
  (let KL = is-left-kan-extension-left-kan-extension-Precategory C D D F F Lk)
  (let α = natural-transformation-left-kan-extension-Precategory C D D F F Lk)
  (let LL = comp-functor-Precategory D D D L L)
  (let LF = comp-functor-Precategory C D D L F)
  (let LLF = comp-functor-Precategory C D D LL F)
  (let LLL = comp-functor-Precategory D D D L LL)
  (let LLLF = comp-functor-Precategory C D D LLL F)
  where

  left-precomp-associative-comul-density-comonad-Precategory :
    comp-natural-transformation-Precategory C D F LF LLLF
      ( right-whisker-natural-transformation-Precategory D D C
        ( L)
        ( LLL)
        ( comp-natural-transformation-Precategory D D L LL LLL
          ( left-whisker-natural-transformation-Precategory D D D L LL
            ( L)
            ( comul-density-comonad-Precategory C D F Lk))
          ( comul-density-comonad-Precategory C D F Lk))
        ( F))
      ( α) ＝
    comp-natural-transformation-Precategory C D F LF LLLF
      ( left-whisker-natural-transformation-Precategory C D D
        ( F)
        ( LLF)
        ( L)
        ( comp-natural-transformation-Precategory C D F LF LLF
          ( left-whisker-natural-transformation-Precategory C D D
            ( F)
            ( LF)
            ( L)
            ( α))
          ( α)))
      ( α)
  left-precomp-associative-comul-density-comonad-Precategory =
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D F LF LLLF x α)
      ( preserves-comp-right-whisker-natural-transformation-Precategory D D C
        ( L)
        ( LL)
        ( LLL)
        ( left-whisker-natural-transformation-Precategory D D D L LL
          ( L)
          ( comul-density-comonad-Precategory C D F Lk))
        ( comul-density-comonad-Precategory C D F Lk)
        ( F))) ∙
    ( associative-comp-natural-transformation-Precategory C D F LF LLF LLLF
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( comp-natural-transformation-Precategory C D F LLF LLLF
        ( right-whisker-natural-transformation-Precategory D D C
          ( LL)
          ( LLL)
          ( left-whisker-natural-transformation-Precategory D D D L LL
            ( L)
            ( comul-density-comonad-Precategory C D F Lk))
            ( F)))
      ( compute-comul-density-comonad-Precategory C D F Lk)) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D F LF LLF LLLF
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D F LF LLLF x α)
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory C D D
          ( F)
          ( LF)
          ( LLF)
          ( L)
          ( right-whisker-natural-transformation-Precategory D D C
            ( L)
            ( LL)
            ( comul-density-comonad-Precategory C D F Lk)
            ( F))
          ( α)))) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D F LF LLLF
        ( left-whisker-natural-transformation-Precategory C D D
          ( F)
          ( LLF)
          ( L)
          ( x))
        ( α))
      ( compute-comul-density-comonad-Precategory C D F Lk))

  right-precomp-associative-comul-density-comonad-Precategory :
    comp-natural-transformation-Precategory C D F LF LLLF
      ( right-whisker-natural-transformation-Precategory D D C
        ( L)
        ( LLL)
        ( comp-natural-transformation-Precategory D D L LL LLL
          ( right-whisker-natural-transformation-Precategory D D D L LL
            ( comul-density-comonad-Precategory C D F Lk)
            ( L))
          ( comul-density-comonad-Precategory C D F Lk))
        ( F))
      ( α) ＝
    comp-natural-transformation-Precategory C D F LF LLLF
      ( left-whisker-natural-transformation-Precategory C D D
        ( F)
        ( LLF)
        ( L)
        ( comp-natural-transformation-Precategory C D F LF LLF
          ( left-whisker-natural-transformation-Precategory C D D
            ( F)
            ( LF)
            ( L)
            ( α))
          ( α)))
      ( α)
  right-precomp-associative-comul-density-comonad-Precategory =
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D F LF LLLF x α)
      ( preserves-comp-right-whisker-natural-transformation-Precategory D D C
        ( L)
        ( LL)
        ( LLL)
        ( right-whisker-natural-transformation-Precategory D D D L LL
          ( comul-density-comonad-Precategory C D F Lk)
          ( L))
        ( comul-density-comonad-Precategory C D F Lk)
        ( F))) ∙
    ( associative-comp-natural-transformation-Precategory C D F LF LLF LLLF
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( comp-natural-transformation-Precategory C D F LLF LLLF
        ( right-whisker-natural-transformation-Precategory D D C
          ( LL)
          ( LLL)
          ( right-whisker-natural-transformation-Precategory D D D L LL
            ( comul-density-comonad-Precategory C D F Lk)
            ( L))
          ( F)))
      ( compute-comul-density-comonad-Precategory C D F Lk)) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D F LF LLF LLLF
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D F LF LLLF x α)
      ( eq-htpy-hom-family-natural-transformation-Precategory C D LF LLLF
        ( _)
        ( _)
        ( λ x →
          inv
            ( naturality-natural-transformation-Precategory D D L LL
              ( comul-density-comonad-Precategory C D F Lk)
              ( _))))) ∙
    ( associative-comp-natural-transformation-Precategory C D F LF LLF LLLF
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D F LLF LLLF
          ( left-whisker-natural-transformation-Precategory C D D
            ( LF)
            ( LLF)
            ( L)
            ( left-whisker-natural-transformation-Precategory C D D
              ( F)
              ( LF)
              ( L)
              ( α)))
          ( x)))
      ( compute-comul-density-comonad-Precategory C D F Lk)) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D F LF LLF LLLF
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D F LF LLLF x α)
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory C D D
          ( F)
          ( LF)
          ( LLF)
          ( L)
          ( left-whisker-natural-transformation-Precategory C D D
            ( F)
            ( LF)
            ( L)
            ( α))
          ( α))))

  abstract
    associative-comul-density-comonad-Precategory :
      comp-natural-transformation-Precategory D D L LL LLL
        ( left-whisker-natural-transformation-Precategory D D D L LL
          ( L)
          ( comul-density-comonad-Precategory C D F Lk))
        ( comul-density-comonad-Precategory C D F Lk) ＝
      comp-natural-transformation-Precategory D D L LL LLL
        ( right-whisker-natural-transformation-Precategory D D D L LL
          ( comul-density-comonad-Precategory C D F Lk)
          ( L))
        ( comul-density-comonad-Precategory C D F Lk)
    associative-comul-density-comonad-Precategory =
      ( inv (is-retraction-map-inv-is-equiv (KL LLL) _)) ∙
      ( ap
        ( map-inv-is-equiv (KL LLL))
        ( ( left-precomp-associative-comul-density-comonad-Precategory) ∙
          ( inv right-precomp-associative-comul-density-comonad-Precategory))) ∙
      ( is-retraction-map-inv-is-equiv (KL LLL) _)
```

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Lk : left-kan-extension-Precategory C D D F F)
  where

  density-comonad-Precategory : comonad-Precategory D
  density-comonad-Precategory =
    ( extension-left-kan-extension-Precategory C D D F F Lk ,
      counit-density-comonad-Precategory C D F Lk) ,
    ( comul-density-comonad-Precategory C D F Lk) ,
    ( ( associative-comul-density-comonad-Precategory C D F Lk) ,
      ( ( left-counit-law-comul-density-comonad-Precategory C D F Lk) ,
        ( right-counit-law-comul-density-comonad-Precategory C D F Lk)))
```

## See also

- [Codensity monads](category-theory.codensity-monads-on-precategories.md) for
  the dual concept
