# Codensity monads on precategories

```agda
module category-theory.codensity-monads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.algebras-monads-on-precategories
open import category-theory.functors-precategories
open import category-theory.monads-on-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.right-extensions-precategories
open import category-theory.right-kan-extensions-precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given an arbitrary [functor](category-theory.functors-precategories.md)
`F : C → D`, any
[right Kan extension](category-theory.right-kan-extensions-precategories.md) `R`
of `F` along itself has a canonical
[monad](category-theory.monads-on-precategories.md) structure, called the
{{#concept "codensity monad" Agda=codensity-monad-Precategory WD="codensity monad" WDID=Q97359844}}
of `R`.

## Monad structure

The unit and multiplication of the codensity monads follow from the "existence"
part of the universal property of the right Kan extension. We use two right
extensions: the identity map on `D` trivially gives a right extension of `D`
along itself, and `R²` gives an extension by whiskering and composing the
natural transformation. By the universal property of `R`, these give natural
transformations `η : id ⇒ R` and `μ : R² ⇒ R`, respectively. From their
definition via the universal property, we have two computation rules for these
natural transformations (where ∙ is whiskering):

1. `α ∘ (η ∙ F) ＝ id_F`; and
2. `α ∘ (μ ∙ F) ＝ α ∘ (R ∙ α)`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Rk : right-kan-extension-Precategory C D D F F)
  (let R = extension-right-kan-extension-Precategory C D D F F Rk)
  (let KR = is-right-kan-extension-right-kan-extension-Precategory C D D F F Rk)
  (let α = natural-transformation-right-kan-extension-Precategory C D D F F Rk)
  (let RR = comp-functor-Precategory D D D R R)
  (let RF = comp-functor-Precategory C D D R F)
  (let RRF = comp-functor-Precategory C D D RR F)
  where

  unit-codensity-monad-Precategory :
    natural-transformation-Precategory D D (id-functor-Precategory D) R
  unit-codensity-monad-Precategory =
    map-inv-is-equiv
      ( KR (id-functor-Precategory D))
      ( pr2 (id-right-extension-Precategory C D F))

  abstract
    compute-unit-codensity-monad-Precategory :
      comp-natural-transformation-Precategory C D F RF F
        ( α)
        ( right-whisker-natural-transformation-Precategory D D C
          ( id-functor-Precategory D)
          ( R)
          ( unit-codensity-monad-Precategory)
          ( F)) ＝
      id-natural-transformation-Precategory C D F
    compute-unit-codensity-monad-Precategory =
      is-section-map-inv-is-equiv
        ( KR (id-functor-Precategory D))
        ( id-natural-transformation-Precategory C D F)

  mul-codensity-monad-Precategory :
    natural-transformation-Precategory D D
      ( comp-functor-Precategory D D D R R)
      ( R)
  mul-codensity-monad-Precategory =
    map-inv-is-equiv
      ( KR (comp-functor-Precategory D D D R R))
      ( pr2
        ( square-right-extension-Precategory C D F
          ( right-extension-right-kan-extension-Precategory C D D F F Rk)))

  abstract
    compute-mul-codensity-monad-Precategory :
      comp-natural-transformation-Precategory C D RRF RF F
        ( α)
        ( right-whisker-natural-transformation-Precategory D D C
          ( RR)
          ( R)
          ( mul-codensity-monad-Precategory)
          ( F)) ＝
      comp-natural-transformation-Precategory C D RRF RF F
        ( α)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( α))
    compute-mul-codensity-monad-Precategory =
      is-section-map-inv-is-equiv (KR RR)
        ( pr2
          ( square-right-extension-Precategory C D F
            ( right-extension-right-kan-extension-Precategory C D D F F Rk)))
```

## Monad laws

Monad laws follow from the "uniqueness" part of the right Kan extension.

### Left unit law

For the left unit law, if `α : R∘F ⇒ F` is the right Kan extension natural
transformation, we show that the composite

```text
      (Rη)F        μF       α
  R∘F ═════>  R²∘F ══>  R∘F ═> R
```

is equal to `α`; by uniqueness, `μF ∘ RμF = id`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Rk : right-kan-extension-Precategory C D D F F)
  (let R = extension-right-kan-extension-Precategory C D D F F Rk)
  (let KR = is-right-kan-extension-right-kan-extension-Precategory C D D F F Rk)
  (let α = natural-transformation-right-kan-extension-Precategory C D D F F Rk)
  (let RR = comp-functor-Precategory D D D R R)
  (let RF = comp-functor-Precategory C D D R F)
  (let RRF = comp-functor-Precategory C D D RR F)
  where

  precomp-left-unit-law-mul-codensity-monad-Precategory :
    right-extension-map-Precategory C D D F F (R , α) R
      ( comp-natural-transformation-Precategory
        D D R RR R
        ( mul-codensity-monad-Precategory C D F Rk)
        ( left-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( R)
          ( unit-codensity-monad-Precategory C D F Rk))) ＝
    α
  precomp-left-unit-law-mul-codensity-monad-Precategory =
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RF RRF RF F
        ( right-whisker-natural-transformation-Precategory D D C R RR
          ( left-whisker-natural-transformation-Precategory D D D
              ( id-functor-Precategory D)
              ( R)
              ( R)
              ( unit-codensity-monad-Precategory C D F Rk))
          ( F))
        ( _)
        ( α))) ∙
    ( ap
      ( λ x →
        comp-natural-transformation-Precategory C D RF RRF F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C R RR
            ( left-whisker-natural-transformation-Precategory D D D
              ( id-functor-Precategory D)
              ( R)
              ( R)
              (unit-codensity-monad-Precategory C D F Rk))
            ( F)))
      ( compute-mul-codensity-monad-Precategory C D F Rk)) ∙
    ( associative-comp-natural-transformation-Precategory C D RF RRF RF F
      ( right-whisker-natural-transformation-Precategory D D C R RR
        ( left-whisker-natural-transformation-Precategory D D D
            ( id-functor-Precategory D)
            ( R)
            ( R)
            ( unit-codensity-monad-Precategory C D F Rk))
        ( F))
      ( _)
      ( α)) ∙
    ( ap
      ( comp-natural-transformation-Precategory C D RF RF F α)
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory
          ( C)
          ( D)
          ( D)
          ( F)
          ( RF)
          ( F)
          ( R)
          ( α)
          ( right-whisker-natural-transformation-Precategory D D C
            ( id-functor-Precategory D)
            ( R)
            ( unit-codensity-monad-Precategory C D F Rk)
            ( F))))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RF RF F
          ( α)
          ( left-whisker-natural-transformation-Precategory C D D F F
            ( R)
            ( x))))
      ( compute-unit-codensity-monad-Precategory C D F Rk)) ∙
    ( ap
      ( comp-natural-transformation-Precategory C D RF RF F α)
      ( preserves-id-left-whisker-natural-transformation-Precategory C D D
        ( F)
        ( R))) ∙
    ( right-unit-law-comp-natural-transformation-Precategory C D RF F α)

  abstract
    left-unit-law-mul-codensity-monad-Precategory :
      comp-natural-transformation-Precategory
        D D R (comp-functor-Precategory D D D R R) R
        ( mul-codensity-monad-Precategory C D F Rk)
        ( left-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( R)
          ( unit-codensity-monad-Precategory C D F Rk)) ＝
      id-natural-transformation-Precategory D D R
    left-unit-law-mul-codensity-monad-Precategory =
      ( inv
        ( is-retraction-map-inv-is-equiv (KR R)
          ( comp-natural-transformation-Precategory D D R RR R
            ( mul-codensity-monad-Precategory C D F Rk)
            ( left-whisker-natural-transformation-Precategory D D D
              ( id-functor-Precategory D)
              ( R)
              ( R)
              ( unit-codensity-monad-Precategory C D F Rk))))) ∙
      ( ap
        ( map-inv-is-equiv (KR R))
        ( ( precomp-left-unit-law-mul-codensity-monad-Precategory) ∙
          ( inv
            ( right-unit-law-comp-natural-transformation-Precategory C D
              ( RF)
              ( F)
              ( α))))) ∙
      ( is-retraction-map-inv-is-equiv
        ( KR R)
        ( id-natural-transformation-Precategory D D R))
```

### Right unit law

The right unit law is similar; we show that the composite is `α` via:

```text
      ηRF      μF     α
   RF ═══> R²F ══> RF ══> F
   ║        ║             ║
 α ║     Rα ║             ║
   ∨        ∨             ║
   F ════> RF ══════════> F
      ηF          α
```

The right square (triangle) commutes by "uniqueness" of the right Kan UP; the
left square commutes by naturality of `η`. The bottom composite is then `id` by
the UP again.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Rk : right-kan-extension-Precategory C D D F F)
  (let R = extension-right-kan-extension-Precategory C D D F F Rk)
  (let KR = is-right-kan-extension-right-kan-extension-Precategory C D D F F Rk)
  (let α = natural-transformation-right-kan-extension-Precategory C D D F F Rk)
  (let RR = comp-functor-Precategory D D D R R)
  (let RF = comp-functor-Precategory C D D R F)
  (let RRF = comp-functor-Precategory C D D RR F)
  where

  precomp-right-unit-law-mul-codensity-monad-Precategory :
    right-extension-map-Precategory C D D F F (R , α) R
      ( comp-natural-transformation-Precategory
        D D R RR R
        ( mul-codensity-monad-Precategory C D F Rk)
        ( right-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( unit-codensity-monad-Precategory C D F Rk)
          ( R))) ＝
    α
  precomp-right-unit-law-mul-codensity-monad-Precategory =
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RF RRF RF F
        ( right-whisker-natural-transformation-Precategory D D C R RR
          ( right-whisker-natural-transformation-Precategory D D D
            ( id-functor-Precategory D)
            ( R)
            ( unit-codensity-monad-Precategory C D F Rk)
            ( R))
          ( F))
        ( right-whisker-natural-transformation-Precategory D D C RR R
          ( mul-codensity-monad-Precategory C D F Rk)
          ( F))
        ( α))) ∙
    ( ap
      ( λ x →
        comp-natural-transformation-Precategory C D RF RRF F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C R RR
            ( right-whisker-natural-transformation-Precategory D D D
              ( id-functor-Precategory D)
              ( R)
              ( unit-codensity-monad-Precategory C D F Rk)
              ( R))
            ( F)))
      ( is-section-map-inv-is-equiv
        ( KR (comp-functor-Precategory D D D R R))
        ( pr2 (square-right-extension-Precategory C D F (pr1 Rk))))) ∙
    ( associative-comp-natural-transformation-Precategory C D RF RRF RF F
      ( right-whisker-natural-transformation-Precategory D D C R RR
        ( right-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( unit-codensity-monad-Precategory C D F Rk)
          ( R))
        ( F))
      ( left-whisker-natural-transformation-Precategory C D D RF F R α)
      ( α)) ∙
    ( ap
      ( comp-natural-transformation-Precategory C D RF RF F α)
      ( eq-htpy-hom-family-natural-transformation-Precategory C D RF RF _ _
        ( λ x →
          ( naturality-natural-transformation-Precategory D D
            ( id-functor-Precategory D)
            ( R)
            ( unit-codensity-monad-Precategory C D F Rk)
            ( pr1 α x))))) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RF F RF F
        ( α)
        ( right-whisker-natural-transformation-Precategory D D C
          ( id-functor-Precategory D)
          ( R)
          ( unit-codensity-monad-Precategory C D F Rk)
          ( F))
        ( α))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RF F F x α))
      ( compute-unit-codensity-monad-Precategory C D F Rk)) ∙
    left-unit-law-comp-natural-transformation-Precategory C D RF F α

  abstract
    right-unit-law-mul-codensity-monad-Precategory :
      comp-natural-transformation-Precategory
        D D R (comp-functor-Precategory D D D R R) R
        ( mul-codensity-monad-Precategory C D F Rk)
        ( right-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( unit-codensity-monad-Precategory C D F Rk)
          ( R)) ＝
      id-natural-transformation-Precategory D D R
    right-unit-law-mul-codensity-monad-Precategory =
      ( inv
        ( is-retraction-map-inv-is-equiv
          ( KR R)
          ( comp-natural-transformation-Precategory D D R RR R
            ( mul-codensity-monad-Precategory C D F Rk)
            ( right-whisker-natural-transformation-Precategory D D D
              ( id-functor-Precategory D) R
              ( unit-codensity-monad-Precategory C D F Rk) R)))) ∙
      ( ap
        ( map-inv-is-equiv (KR R))
        ( ( precomp-right-unit-law-mul-codensity-monad-Precategory) ∙
          ( inv
            ( right-unit-law-comp-natural-transformation-Precategory C D
              ( RF)
              ( F)
              ( α))))) ∙
      ( is-retraction-map-inv-is-equiv
        ( KR R)
        ( id-natural-transformation-Precategory D D R))
```

### Multiplication is associative

Showing that multiplication is associative is similar but longer.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Rk : right-kan-extension-Precategory C D D F F)
  (let R = extension-right-kan-extension-Precategory C D D F F Rk)
  (let KR = is-right-kan-extension-right-kan-extension-Precategory C D D F F Rk)
  (let α = natural-transformation-right-kan-extension-Precategory C D D F F Rk)
  (let RR = comp-functor-Precategory D D D R R)
  (let RF = comp-functor-Precategory C D D R F)
  (let RRF = comp-functor-Precategory C D D RR F)
  (let RRR = comp-functor-Precategory D D D R RR)
  (let RRRF = comp-functor-Precategory C D D RRR F)
  where

  left-precomp-associative-mul-codensity-monad-Precategory :
    comp-natural-transformation-Precategory C D RRRF RF F
      ( α)
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( R)
        ( comp-natural-transformation-Precategory D D RRR RR R
          ( mul-codensity-monad-Precategory C D F Rk)
          ( left-whisker-natural-transformation-Precategory D D D RR R
            ( R)
            ( mul-codensity-monad-Precategory C D F Rk)))
        ( F)) ＝
    comp-natural-transformation-Precategory C D RRRF RF F
      ( α)
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( F)
        ( R)
        ( comp-natural-transformation-Precategory C D RRF RF F
          ( α)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( α))))
  left-precomp-associative-mul-codensity-monad-Precategory =
    ( ap
      ( comp-natural-transformation-Precategory C D RRRF RF F α)
      ( preserves-comp-right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( R)
        ( mul-codensity-monad-Precategory C D F Rk)
        ( left-whisker-natural-transformation-Precategory D D D RR R
          ( R)
          ( mul-codensity-monad-Precategory C D F Rk))
        ( F))) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( right-whisker-natural-transformation-Precategory D D C
          ( RRR)
          ( RR)
          ( left-whisker-natural-transformation-Precategory D D D RR R
            ( R)
            ( mul-codensity-monad-Precategory C D F Rk))
          ( F))
        ( right-whisker-natural-transformation-Precategory D D C RR R
          ( mul-codensity-monad-Precategory C D F Rk)
          ( F))
        ( α))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RRRF RRF F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C
            ( RRR)
            ( RR)
            ( left-whisker-natural-transformation-Precategory D D D RR R
              ( R)
              ( mul-codensity-monad-Precategory C D F Rk))
            ( F))))
      ( compute-mul-codensity-monad-Precategory C D F Rk)) ∙
    ( associative-comp-natural-transformation-Precategory C D
      ( RRRF)
      ( RRF)
      ( RF)
      ( F)
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( left-whisker-natural-transformation-Precategory D D D RR R
          ( R)
          ( mul-codensity-monad-Precategory C D F Rk))
        ( F))
      ( _)
      ( α)) ∙
    ( ap
      ( comp-natural-transformation-Precategory C D RRRF RF F α)
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( RF)
          ( F)
          ( R)
          ( α)
          ( right-whisker-natural-transformation-Precategory D D C
            ( RR)
            ( R)
            ( mul-codensity-monad-Precategory C D F Rk)
            ( F))))) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D RRRF RF F
        ( α)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( F)
          ( R)
          ( x)))
      ( compute-mul-codensity-monad-Precategory C D F Rk))

  right-precomp-associative-mul-codensity-monad-Precategory :
    comp-natural-transformation-Precategory C D RRRF RF F
      ( α)
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( R)
        ( comp-natural-transformation-Precategory D D RRR RR R
          ( mul-codensity-monad-Precategory C D F Rk)
          ( right-whisker-natural-transformation-Precategory D D D RR R
            ( mul-codensity-monad-Precategory C D F Rk)
            ( R)))
        ( F)) ＝
    comp-natural-transformation-Precategory C D RRRF RF F
      ( α)
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( F)
        ( R)
        ( comp-natural-transformation-Precategory C D RRF RF F
          ( α)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( α))))
  right-precomp-associative-mul-codensity-monad-Precategory =
    ( ap
      ( comp-natural-transformation-Precategory C D RRRF RF F α)
      ( preserves-comp-right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( R)
        ( mul-codensity-monad-Precategory C D F Rk)
        ( right-whisker-natural-transformation-Precategory D D D RR R
          ( mul-codensity-monad-Precategory C D F Rk)
          ( R))
        ( F))) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RRRF RRF F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C
            ( RRR)
            ( RR)
            ( right-whisker-natural-transformation-Precategory D D D RR R
              ( mul-codensity-monad-Precategory C D F Rk)
              ( R))
            ( F))))
      ( compute-mul-codensity-monad-Precategory C D F Rk)) ∙
    ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _)) ∙
    ( ap
      ( comp-natural-transformation-Precategory C D RRRF RF F α)
      ( eq-htpy-hom-family-natural-transformation-Precategory C D RRRF RF
        ( _)
        ( _)
        ( λ x →
          naturality-natural-transformation-Precategory D D RR R
            ( mul-codensity-monad-Precategory C D F Rk)
            ( _)))) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RRRF RRF F
          ( x)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RRF)
            ( RF)
            ( R)
            ( left-whisker-natural-transformation-Precategory C D D
              ( RF)
              ( F)
              ( R)
              ( α)))))
      ( compute-mul-codensity-monad-Precategory C D F Rk)) ∙
    ( associative-comp-natural-transformation-Precategory C D
      ( RRRF)
      ( RRF)
      ( RF)
      ( F)
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( comp-natural-transformation-Precategory C D RRRF RF F α)
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( RF)
          ( F)
          ( R)
          ( α)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( α)))))

  abstract
    associative-mul-codensity-monad-Precategory :
      comp-natural-transformation-Precategory D D RRR RR R
        ( mul-codensity-monad-Precategory C D F Rk)
        ( left-whisker-natural-transformation-Precategory D D D RR R
          ( R)
          ( mul-codensity-monad-Precategory C D F Rk)) ＝
      comp-natural-transformation-Precategory D D RRR RR R
        ( mul-codensity-monad-Precategory C D F Rk)
        ( right-whisker-natural-transformation-Precategory D D D RR R
          ( mul-codensity-monad-Precategory C D F Rk)
          ( R))
    associative-mul-codensity-monad-Precategory =
      ( inv (is-retraction-map-inv-is-equiv (KR RRR) _)) ∙
      ( ap
        ( map-inv-is-equiv (KR RRR))
        ( ( left-precomp-associative-mul-codensity-monad-Precategory) ∙
          ( inv right-precomp-associative-mul-codensity-monad-Precategory))) ∙
      ( is-retraction-map-inv-is-equiv (KR RRR) _)
```

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Rk : right-kan-extension-Precategory C D D F F)
  where

  codensity-monad-Precategory : monad-Precategory D
  codensity-monad-Precategory =
    ( extension-right-kan-extension-Precategory C D D F F Rk ,
      unit-codensity-monad-Precategory C D F Rk) ,
    ( mul-codensity-monad-Precategory C D F Rk) ,
    ( ( associative-mul-codensity-monad-Precategory C D F Rk) ,
      ( ( left-unit-law-mul-codensity-monad-Precategory C D F Rk) ,
        ( right-unit-law-mul-codensity-monad-Precategory C D F Rk)))
```

## See also

- [Density comonads](category-theory.density-comonads-on-precategories.md) for
  the dual concept

## External links

- [Codensity monad](https://ncatlab.org/nlab/show/codensity+monad) at $n$Lab
- [Codensity monad](https://en.wikipedia.org/wiki/Codensity_monad) at Wikipedia
