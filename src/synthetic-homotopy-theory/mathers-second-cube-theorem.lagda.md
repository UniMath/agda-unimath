# Mather's second cube theorem

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.mathers-second-cube-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.pullbacks
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

{{#concept "Mather's second cube theorem" Disambiguation="for types"}} states
that every base change of a [pushout](synthetic-homotopy-theory.pushouts.md)
square is a pushout. In other words, if we are given a
[commuting cube](foundation.commuting-cubes-of-maps.md) where the bottom face is
a pushout and the vertical faces are [pullbacks](foundation-core.pullbacks.md)

```text
  ∙ ----------------> ∙
  |⌟\ ⌟               |⌟\
  |  \                |  \
  |   ∨               |   ∨
  |     ∙ ----------------> ∙
  |     | ⌟           |     |
  ∨     |             ∨     |
  ∙ ----|-----------> ∙     |
    \   |               \   |
     \  |                \  |
      ∨ ∨               ⌜ ∨ ∨
        ∙ ----------------> ∙,
```

then the top face is also a pushout.

## Theorem

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (left : f ∘ hA ~ hB ∘ f')
  (back : g ∘ hA ~ hC ∘ g')
  (front : h ∘ hB ~ hD ∘ h')
  (right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top left back front right bottom)
  where

  mathers-second-cube-theorem :
    universal-property-pushout f g (h , k , bottom) →
    universal-property-pullback h hD (hB , h' , front) →
    universal-property-pullback k hD (hC , k' , right) →
    universal-property-pullback f hB (hA , f' , left) →
    universal-property-pullback g hC (hA , g' , back) →
    universal-property-pushout f' g' (h' , k' , top)
  mathers-second-cube-theorem po-bottom pb-front pb-right pb-left pb-back =
    up-top
    where
      e-left =
        fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
          f hB (hA , f' , left) pb-left
      e-front =
        fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
          h hD (hB , h' , front) pb-front
      e-right =
        fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
          k hD (hC , k' , right) pb-right
      P :
        descent-data-pushout
          ( make-span-diagram f g)
          ( l2' ⊔ l2)
          ( l3' ⊔ l3)
      P =
        ( fiber' hB ,
          fiber' hC ,
          ( λ s →
            ( inv-equiv (e-right (g s))) ∘e
            ( equiv-tr (fiber' hD) (bottom s)) ∘e
            ( e-front (f s))))

      e :
        equiv-descent-data-pushout
          P
          ( descent-data-family-cocone-span-diagram
            ( h , k , bottom)
            ( fiber' hD))
      e =
        ( e-front ,
          e-right ,
          ( λ s t →
            is-section-map-inv-equiv
              ( e-right (g s))
              ( tr
                ( fiber' hD)
                ( bottom s)
                ( map-equiv (e-front (f s)) t))))

      cocone-flat-Σ :
        cocone
          ( vertical-map-span-flattening-descent-data-pushout P)
          ( horizontal-map-span-flattening-descent-data-pushout P)
          ( Σ D (fiber' hD))
      cocone-flat-Σ =
        cocone-flattening-descent-data-pushout
          ( f)
          ( g)
          ( h , k , bottom)
          ( P)
          ( fiber' hD)
          ( e)

      up-cocone-flat-Σ :
        universal-property-pushout
          ( vertical-map-span-flattening-descent-data-pushout P)
          ( horizontal-map-span-flattening-descent-data-pushout P)
          ( cocone-flat-Σ)
      up-cocone-flat-Σ =
        flattening-lemma-descent-data-pushout
          ( f)
          ( g)
          ( h , k , bottom)
          ( P)
          ( fiber' hD)
          ( e)
          ( po-bottom)

      cocone-flat :
        cocone
          ( vertical-map-span-flattening-descent-data-pushout P)
          ( horizontal-map-span-flattening-descent-data-pushout P)
          D'
      cocone-flat =
        cocone-map
          ( vertical-map-span-flattening-descent-data-pushout P)
          ( horizontal-map-span-flattening-descent-data-pushout P)
          ( cocone-flat-Σ)
          ( map-equiv (equiv-total-fiber' hD))

      compute-vertical-map-cocone-flat :
        (t : Σ C (fiber' hC)) →
        pr1 (pr2 cocone-flat) t ＝
        pr1
          ( map-equiv
            ( e-right (pr1 t))
            ( pr2 t))
      compute-vertical-map-cocone-flat t = refl

      up-cocone-flat :
        universal-property-pushout
          ( vertical-map-span-flattening-descent-data-pushout P)
          ( horizontal-map-span-flattening-descent-data-pushout P)
          ( cocone-flat)
      up-cocone-flat =
        up-pushout-up-pushout-is-equiv
          ( vertical-map-span-flattening-descent-data-pushout P)
          ( horizontal-map-span-flattening-descent-data-pushout P)
          ( cocone-flat-Σ)
          ( cocone-flat)
          ( map-equiv (equiv-total-fiber' hD))
          ( refl-htpy-cocone
            ( vertical-map-span-flattening-descent-data-pushout P)
            ( horizontal-map-span-flattening-descent-data-pushout P)
            ( cocone-flat))
          ( is-equiv-map-equiv-total-fiber' hD)
          ( up-cocone-flat-Σ)

      left-square :
        coherence-square-maps
          ( f')
          ( map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))
          ( map-equiv (inv-equiv-total-fiber' hB))
          ( vertical-map-span-flattening-descent-data-pushout P)
      left-square x =
        eq-pair-Σ (left x) (inv-compute-tr-self-fiber' hB (f' x , left x))

      source-front : (x : A') → fiber' hD (h (f (hA x)))
      source-front x =
        map-equiv
          ( e-front (f (hA x)))
          ( map-equiv (e-left (hA x)) (x , refl))

      compute-source-front :
        (x : A') →
        source-front x ＝ (h' (f' x) , ap h (left x) ∙ front (f' x))
      compute-source-front x = refl

      compute-tr-source-front :
        (x : A') →
        tr (fiber' hD) (bottom (hA x)) (source-front x) ＝
        ( h' (f' x) ,
          inv (bottom (hA x)) ∙ (ap h (left x) ∙ front (f' x)))
      compute-tr-source-front x =
        ( inv-compute-tr-fiber' hD (bottom (hA x)) (source-front x)) ∙
        ( ap
          ( tot (λ y q → inv (bottom (hA x)) ∙ q))
          ( compute-source-front x))

      coherence-front-right :
        (x : A') →
        ( h' (f' x) ,
          inv (bottom (hA x)) ∙ (ap h (left x) ∙ front (f' x))) ＝
        (k' (g' x) , ap k (back x) ∙ right (g' x))
      coherence-front-right x =
        eq-pair-Σ
          ( top x)
          ( ( inv
              ( substitution-law-tr
                ( λ y → (k ∘ g) (hA x) ＝ y)
                ( hD)
                ( top x))) ∙
            ( tr-Id-right
              ( ap hD (top x))
              ( inv (bottom (hA x)) ∙ (ap h (left x) ∙ front (f' x)))) ∙
            ( assoc
              ( inv (bottom (hA x)))
              ( ap h (left x) ∙ front (f' x))
              ( ap hD (top x))) ∙
            ( inv
              ( left-transpose-eq-concat
                ( bottom (hA x))
                ( ap k (back x) ∙ right (g' x))
                ( ( ap h (left x) ∙ front (f' x)) ∙ ap hD (top x))
                ( inv (c x)))))

      ap-pr1-coherence-front-right :
        (x : A') →
        ap pr1 (coherence-front-right x) ＝ top x
      ap-pr1-coherence-front-right x =
        ap-pr1-eq-pair-Σ
          ( top x)
          ( ( inv
              ( substitution-law-tr
                ( λ y → (k ∘ g) (hA x) ＝ y)
                ( hD)
                ( top x))) ∙
            ( tr-Id-right
              ( ap hD (top x))
              ( inv (bottom (hA x)) ∙ (ap h (left x) ∙ front (f' x)))) ∙
            ( assoc
              ( inv (bottom (hA x)))
              ( ap h (left x) ∙ front (f' x))
              ( ap hD (top x))) ∙
            ( inv
              ( left-transpose-eq-concat
                ( bottom (hA x))
                ( ap k (back x) ∙ right (g' x))
                ( ( ap h (left x) ∙ front (f' x)) ∙ ap hD (top x))
                ( inv (c x)))))

      compute-right :
        (x : A') →
        map-equiv (e-right (g (hA x))) (g' x , back x) ＝
        (k' (g' x) , ap k (back x) ∙ right (g' x))
      compute-right x = refl

      ap-pr1-compute-right :
        (x : A') →
        ap pr1 (compute-right x) ＝ refl
      ap-pr1-compute-right x = refl

      coherence-tr-front-right :
        (x : A') →
        tr (fiber' hD) (bottom (hA x)) (source-front x) ＝
        map-equiv (e-right (g (hA x))) (g' x , back x)
      coherence-tr-front-right x =
        ( compute-tr-source-front x) ∙
        ( coherence-front-right x) ∙
        ( inv (compute-right x))

      ap-pr1-coherence-tr-front-right :
        (x : A') →
        ap pr1 (coherence-tr-front-right x) ＝
        ( ( ap pr1 (compute-tr-source-front x) ∙
            ap pr1 (coherence-front-right x)) ∙
          ap pr1 (inv (compute-right x)))
      ap-pr1-coherence-tr-front-right x =
        ( ap-concat
          ( pr1)
          ( compute-tr-source-front x ∙ coherence-front-right x)
          ( inv (compute-right x))) ∙
          ( ap
            ( λ p → p ∙ ap pr1 (inv (compute-right x)))
            ( ap-concat
              ( pr1)
              ( compute-tr-source-front x)
              ( coherence-front-right x)))

      back-source : (x : A') → fiber' hC (g (hA x))
      back-source x =
        map-family-descent-data-pushout
          ( P)
          ( hA x)
          ( pr2 (map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA) x))

      compute-back-source :
        (x : A') →
        back-source x ＝
        map-inv-equiv
          ( e-right (g (hA x)))
          ( tr (fiber' hD) (bottom (hA x)) (source-front x))
      compute-back-source x = refl

      coherence-back-source :
        (x : A') → back-source x ＝ (g' x , back x)
      coherence-back-source x =
        ( compute-back-source x) ∙
        ( ap
          ( map-inv-equiv (e-right (g (hA x))))
          ( coherence-tr-front-right x)) ∙
        ( is-retraction-map-inv-equiv (e-right (g (hA x))) (g' x , back x))

      back-path :
        (x : A') →
        tr (fiber' hC) (back x) (back-source x) ＝ (g' x , refl)
      back-path x =
        ( ap (tr (fiber' hC) (back x)) (coherence-back-source x)) ∙
        ( inv-compute-tr-self-fiber' hC (g' x , back x))

      right-square :
        coherence-square-maps
          ( g')
          ( map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))
          ( map-equiv (inv-equiv-total-fiber' hC))
          ( horizontal-map-span-flattening-descent-data-pushout P)
      right-square x =
        eq-pair-Σ (back x) (back-path x)

      first-term-top-flat : (x : A') → h' (f' x) ＝ k' (pr1 (back-source x))
      first-term-top-flat x =
        ap (pr1 cocone-flat) (inv (left-square x)) ∙
        (pr2 (pr2 cocone-flat) ·r map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA)) x

      third-term-top-flat :
        (x : A') →
        k' (pr1 (back-source x)) ＝
        k' (g' x)
      third-term-top-flat x =
        (pr1 (pr2 (cocone-comp-horizontal
          ( f')
          ( map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))
          ( horizontal-map-span-flattening-descent-data-pushout P)
          ( map-equiv (inv-equiv-total-fiber' hB) ,
            vertical-map-span-flattening-descent-data-pushout P ,
            inv-htpy left-square)
          ( cocone-flat))) ·l right-square) x

      third-term-top-flat-compute :
        (x : A') →
        third-term-top-flat x ＝
        ap
          ( pr1 (pr2 cocone-flat))
          ( right-square x)
      third-term-top-flat-compute x = refl

      middle-term-top-flat :
        (x : A') →
        k' (pr1 (back-source x)) ＝
        pr1 (tr (fiber' hD) (bottom (hA x)) (source-front x))
      middle-term-top-flat x =
        ( ap
          ( λ t →
            pr1
              ( map-equiv
                ( e-right (g (hA x)))
                ( t)))
          ( compute-back-source x)) ∙
        ( ap pr1
          ( is-section-map-inv-equiv
            ( e-right (g (hA x)))
            ( tr (fiber' hD) (bottom (hA x)) (source-front x))))

      up-top-flat :
        universal-property-pushout
          f'
          g'
          ( comp-cocone-hom-span
            ( vertical-map-span-flattening-descent-data-pushout P)
            ( horizontal-map-span-flattening-descent-data-pushout P)
            ( f')
            ( g')
            ( map-equiv (inv-equiv-total-fiber' hB))
            ( map-equiv (inv-equiv-total-fiber' hC))
            ( map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))
            ( cocone-flat)
            ( inv-htpy left-square)
            ( right-square))
      up-top-flat =
        universal-property-pushout-extended-by-equivalences
          ( vertical-map-span-flattening-descent-data-pushout P)
          ( horizontal-map-span-flattening-descent-data-pushout P)
          ( f')
          ( g')
          ( map-equiv (inv-equiv-total-fiber' hB))
          ( map-equiv (inv-equiv-total-fiber' hC))
          ( map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))
          ( cocone-flat)
          ( up-cocone-flat)
          ( inv-htpy left-square)
          ( right-square)
          ( is-equiv-map-inv-equiv-total-fiber' hB)
          ( is-equiv-map-inv-equiv-total-fiber' hC)
          ( is-equiv-map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))

      cocone-top-flat : cocone f' g' D'
      cocone-top-flat =
        comp-cocone-hom-span
          ( vertical-map-span-flattening-descent-data-pushout P)
          ( horizontal-map-span-flattening-descent-data-pushout P)
          ( f')
          ( g')
          ( map-equiv (inv-equiv-total-fiber' hB))
          ( map-equiv (inv-equiv-total-fiber' hC))
          ( map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))
          ( cocone-flat)
          ( inv-htpy left-square)
          ( right-square)

      horizontal-cocone-top-flat : horizontal-map-cocone f' g' cocone-top-flat ~ h'
      horizontal-cocone-top-flat x = refl

      vertical-cocone-top-flat : vertical-map-cocone f' g' cocone-top-flat ~ k'
      vertical-cocone-top-flat x = refl

      path-coherence-cocone-top-flat : (x : A') → h' (f' x) ＝ k' (g' x)
      path-coherence-cocone-top-flat x =
        first-term-top-flat x ∙ third-term-top-flat x

      module MiddleThirdTopFlatTarget (x : A') where
        eR : fiber' hC (g (hA x)) ≃ fiber' hD (k (g (hA x)))
        eR = e-right (g (hA x))

        u : fiber' hD (k (g (hA x)))
        u = tr (fiber' hD) (bottom (hA x)) (source-front x)

        v : fiber' hD (k (g (hA x)))
        v = map-equiv eR (g' x , back x)

        F : fiber' hC (g (hA x)) → D'
        F t = pr1 (map-equiv eR t)

        π : fiber' hD (k (g (hA x))) → D'
        π = pr1

        H :
          ( λ t →
            pr1
              ( map-equiv
                ( e-right (g (hA x)))
                ( map-inv-equiv eR t))) ~
          π
        H t =
          ap π (is-section-map-inv-equiv eR t)

        section-to-retraction :
          ap π (is-section-map-inv-equiv eR v) ＝
          ap F (is-retraction-map-inv-equiv eR (g' x , back x))
        section-to-retraction =
          ( ap (ap π) (coherence-map-inv-equiv eR (g' x , back x))) ∙
          ( inv
            ( ap-comp
              ( π)
              ( map-equiv eR)
              ( is-retraction-map-inv-equiv eR (g' x , back x))))

        abstract
          proof :
            middle-term-top-flat x ∙
            ap pr1 (coherence-tr-front-right x) ＝
            ap
              ( λ t →
                pr1
                  ( map-equiv
                    ( e-right (g (hA x)))
                    ( t)))
              ( coherence-back-source x)
          proof =
            ( assoc
              ( ap F (compute-back-source x))
              ( ap π (is-section-map-inv-equiv eR u))
              ( ap π (coherence-tr-front-right x))) ∙
            ( ap
              ( λ p → ap F (compute-back-source x) ∙ p)
              ( nat-htpy H (coherence-tr-front-right x))) ∙
            ( inv
              ( assoc
                ( ap F (compute-back-source x))
                ( ap (F ∘ map-inv-equiv eR) (coherence-tr-front-right x))
                ( ap π (is-section-map-inv-equiv eR v)))) ∙
            ( ap
              ( λ q →
                ( ap F (compute-back-source x) ∙ q) ∙
                ap π (is-section-map-inv-equiv eR v))
              ( ap-comp F (map-inv-equiv eR) (coherence-tr-front-right x))) ∙
            ( ap
              ( λ p → p ∙ ap π (is-section-map-inv-equiv eR v))
              ( inv
                ( ap-concat
                  ( F)
                  ( compute-back-source x)
                  ( ap (map-inv-equiv eR) (coherence-tr-front-right x))))) ∙
            ( ap
              ( λ p →
                ap F
                  ( compute-back-source x ∙
                    ap (map-inv-equiv eR) (coherence-tr-front-right x)) ∙
                p)
              section-to-retraction) ∙
            ( inv
              ( ap-concat
                ( F)
                ( compute-back-source x ∙
                  ap (map-inv-equiv eR) (coherence-tr-front-right x))
                ( is-retraction-map-inv-equiv eR (g' x , back x))))

      abstract
        middle-third-top-flat-target :
          (x : A') →
          middle-term-top-flat x ∙
          ap pr1 (coherence-tr-front-right x) ＝
          ap
            ( λ t →
              pr1
                ( map-equiv
                  ( e-right (g (hA x)))
                  ( t)))
            ( coherence-back-source x)
        middle-third-top-flat-target x = MiddleThirdTopFlatTarget.proof x

      module FirstMiddleTopFlat (x : A') where
        eR : fiber' hC (g (hA x)) ≃ fiber' hD (k (g (hA x)))
        eR = e-right (g (hA x))

        u : fiber' hD (k (g (hA x)))
        u = tr (fiber' hD) (bottom (hA x)) (source-front x)

        q =
          ( pr2 (pr2 cocone-flat) ·r
            map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA)) x

        r = middle-term-top-flat x

        pr1-pr2-B : Σ B (fiber' hB) → B'
        pr1-pr2-B t = pr1 (pr2 t)

        pr1-pr2-D : Σ D (fiber' hD) → D'
        pr1-pr2-D t = pr1 (pr2 t)

        ap-pr1-compute-tr-self-fiber'-compute-tr-fiber'-B :
          {y : B} (v : fiber' hB y) →
          ap pr1 (compute-tr-self-fiber' hB v) ＝
          ap pr1 (compute-tr-fiber' hB (pr2 v) v)
        ap-pr1-compute-tr-self-fiber'-compute-tr-fiber'-B (._ , refl) = refl

        ap-pr1-inv-compute-tr-self-fiber'-htpy-B :
          {y : B} (v : fiber' hB y) →
          ap pr1 (inv-compute-tr-self-fiber' hB v) ＝
          inv (ap pr1 (compute-tr-fiber' hB (pr2 v) v))
        ap-pr1-inv-compute-tr-self-fiber'-htpy-B v =
          ( ap-inv pr1 (compute-tr-self-fiber' hB v)) ∙
          ( ap inv (ap-pr1-compute-tr-self-fiber'-compute-tr-fiber'-B v))

        ap-pr1-pr2-eq-pair-Σ-B :
          {y y' : B} (p : y ＝ y') (v : fiber' hB y) →
          ap pr1-pr2-B (eq-pair-Σ p refl) ＝
          ap pr1 (compute-tr-fiber' hB p v)
        ap-pr1-pr2-eq-pair-Σ-B refl v = refl

        ap-pr1-pr2-left-square :
          ap pr1-pr2-B (left-square x) ＝ refl
        ap-pr1-pr2-left-square =
          ( compute-ap-eq-pair-Σ
            ( pr1-pr2-B)
            ( left x)
            ( inv-compute-tr-self-fiber' hB (f' x , left x))) ∙
          ( ap
            ( λ p →
              p ∙ ap pr1 (inv-compute-tr-self-fiber' hB (f' x , left x)))
            ( ap-pr1-pr2-eq-pair-Σ-B (left x) (f' x , left x))) ∙
          ( ap
            ( λ p →
              ap pr1
                ( compute-tr-fiber' hB (left x) (f' x , left x)) ∙
              p)
            ( ap-pr1-inv-compute-tr-self-fiber'-htpy-B (f' x , left x))) ∙
          ( right-inv
            ( ap pr1 (compute-tr-fiber' hB (left x) (f' x , left x))))

        ap-pr1-cocone-flat-left-square :
          ap (pr1 cocone-flat) (left-square x) ＝ refl
        ap-pr1-cocone-flat-left-square =
          ( ap-comp h' pr1-pr2-B (left-square x)) ∙
          ( ap (ap h') ap-pr1-pr2-left-square) ∙
          ( ap-refl h' (f' x))

        ap-pr1-cocone-flat-inv-left-square :
          ap (pr1 cocone-flat) (inv (left-square x)) ＝ refl
        ap-pr1-cocone-flat-inv-left-square =
          ( ap-inv (pr1 cocone-flat) (left-square x)) ∙
          ( ap inv ap-pr1-cocone-flat-left-square)

        ap-pr1-pr2-eq-pair-Σ-D :
          {y y' : D} (p : y ＝ y') (v : fiber' hD y) →
          ap pr1-pr2-D (eq-pair-Σ p refl) ＝
          ap pr1 (compute-tr-fiber' hD p v)
        ap-pr1-pr2-eq-pair-Σ-D refl v = refl

        coherence-top-flat :
          q ＝
          ap pr1
            ( compute-tr-fiber' hD (bottom (hA x)) (source-front x)) ∙
          ap pr1 (inv (is-section-map-inv-equiv eR u))
        coherence-top-flat =
          ( compute-ap-eq-pair-Σ
            ( pr1-pr2-D)
            ( bottom (hA x))
            ( inv (is-section-map-inv-equiv eR u))) ∙
          ( ap
            ( λ p → p ∙ ap pr1 (inv (is-section-map-inv-equiv eR u)))
            ( ap-pr1-pr2-eq-pair-Σ-D
              ( bottom (hA x))
              ( source-front x)))

        middle-term-top-flat-rewrite :
          middle-term-top-flat x ＝
          ap pr1 (is-section-map-inv-equiv eR u)
        middle-term-top-flat-rewrite = refl

        cancel-is-section :
          ap pr1 (inv (is-section-map-inv-equiv eR u)) ∙
          middle-term-top-flat x ＝
          refl
        cancel-is-section =
          ( ap
            ( λ p → ap pr1 (inv (is-section-map-inv-equiv eR u)) ∙ p)
            ( middle-term-top-flat-rewrite)) ∙
          ( ap
            ( λ p → p ∙ ap pr1 (is-section-map-inv-equiv eR u))
            ( ap-inv pr1 (is-section-map-inv-equiv eR u))) ∙
          ( left-inv (ap pr1 (is-section-map-inv-equiv eR u)))

        ap-pr1-ap-tot-compute-source-front :
          ap pr1
            ( ap
              ( tot (λ y q → inv (bottom (hA x)) ∙ q))
              ( compute-source-front x)) ＝
          refl
        ap-pr1-ap-tot-compute-source-front =
          ( inv
            ( ap-comp
              ( pr1)
              ( tot (λ y q → inv (bottom (hA x)) ∙ q))
              ( compute-source-front x))) ∙
          ( ap-refl
            ( pr1 ∘ tot (λ y q → inv (bottom (hA x)) ∙ q))
            ( source-front x))

        ap-pr1-compute-tr-source-front :
          ap pr1 (compute-tr-source-front x) ＝
          ap pr1
            ( inv-compute-tr-fiber' hD (bottom (hA x)) (source-front x))
        ap-pr1-compute-tr-source-front =
          ( ap-concat
            ( pr1)
            ( inv-compute-tr-fiber' hD (bottom (hA x)) (source-front x))
            ( ap
              ( tot (λ y q → inv (bottom (hA x)) ∙ q))
              ( compute-source-front x))) ∙
          ( ap
            ( λ p →
              ap pr1
                ( inv-compute-tr-fiber' hD (bottom (hA x)) (source-front x)) ∙
              p)
            ( ap-pr1-ap-tot-compute-source-front)) ∙
          ( right-unit)

        inv-ap-pr1-inv-compute-tr-fiber' :
          inv
            ( ap pr1
              ( inv-compute-tr-fiber' hD (bottom (hA x)) (source-front x))) ＝
          ap pr1 (compute-tr-fiber' hD (bottom (hA x)) (source-front x))
        inv-ap-pr1-inv-compute-tr-fiber' =
          ( ap inv
            ( ap-inv pr1
              ( compute-tr-fiber' hD (bottom (hA x)) (source-front x)))) ∙
          ( inv-inv
            ( ap pr1
              ( compute-tr-fiber' hD (bottom (hA x)) (source-front x))))

        inv-ap-pr1-compute-tr-source-front :
          ap pr1
            ( compute-tr-fiber' hD (bottom (hA x)) (source-front x)) ＝
          inv (ap pr1 (compute-tr-source-front x))
        inv-ap-pr1-compute-tr-source-front =
          ( inv inv-ap-pr1-inv-compute-tr-fiber') ∙
          ( inv (ap inv ap-pr1-compute-tr-source-front))

        abstract
          proof :
            first-term-top-flat x ∙ middle-term-top-flat x ＝
            inv (ap pr1 (compute-tr-source-front x))
          proof =
            ( assoc
              ( ap (pr1 cocone-flat) (inv (left-square x)))
              ( q)
              ( r)) ∙
            ( ap
              ( λ p → p ∙ (q ∙ r))
              ( ap-pr1-cocone-flat-inv-left-square)) ∙
            ( left-unit {p = q ∙ r}) ∙
            ( ap
              ( λ p → p ∙ r)
              ( coherence-top-flat)) ∙
            ( assoc
              ( ap pr1
                ( compute-tr-fiber' hD (bottom (hA x)) (source-front x)))
              ( ap pr1 (inv (is-section-map-inv-equiv eR u)))
              ( r)) ∙
            ( ap
              ( λ p →
                ap pr1
                  ( compute-tr-fiber' hD (bottom (hA x)) (source-front x)) ∙
                p)
              ( cancel-is-section)) ∙
            ( right-unit) ∙
            ( inv-ap-pr1-compute-tr-source-front)

      abstract
        first-middle-top-flat-test :
          (x : A') →
          first-term-top-flat x ∙ middle-term-top-flat x ＝
          inv (ap pr1 (compute-tr-source-front x))
        first-middle-top-flat-test x = FirstMiddleTopFlat.proof x

      third-term-top-flat-target :
        (x : A') →
        ap
          ( λ t →
            pr1
              ( map-equiv
                ( e-right (g (hA x)))
                ( t)))
          ( coherence-back-source x) ＝
        third-term-top-flat x
      third-term-top-flat-target x =
        ( ap-pr1-map-equiv-e-right) ∙
        ( ap-comp k' pr1 (coherence-back-source x)) ∙
        ( inv (ap (ap k') (ap-pr1-pr2-right-square))) ∙
        ( inv (ap-comp k' pr1-pr2 (right-square x))) ∙
        ( inv ap-pr1-vertical-map-cocone-flat) ∙
        ( inv (third-term-top-flat-compute x))
        where
          pr1-map-equiv-e-right' :
            {c : C} (t : fiber' hC c) →
            pr1 (map-equiv (e-right c) t) ＝ k' (pr1 t)
          pr1-map-equiv-e-right' t = refl

          pr1-map-equiv-e-right :
            (t : fiber' hC (g (hA x))) →
            pr1 (map-equiv (e-right (g (hA x))) t) ＝ k' (pr1 t)
          pr1-map-equiv-e-right t = pr1-map-equiv-e-right' t

          pr1-pr2 : Σ C (fiber' hC) → C'
          pr1-pr2 t = pr1 (pr2 t)

          pr1-vertical-map-cocone-flat :
            (t : Σ C (fiber' hC)) →
            pr1 (pr2 cocone-flat) t ＝ k' (pr1 (pr2 t))
          pr1-vertical-map-cocone-flat t =
            ( compute-vertical-map-cocone-flat t) ∙
            ( pr1-map-equiv-e-right' (pr2 t))

          ap-pr1-vertical-map-cocone-flat :
            ap (pr1 (pr2 cocone-flat)) (right-square x) ＝
            ap (k' ∘ pr1-pr2) (right-square x)
          ap-pr1-vertical-map-cocone-flat =
            ( ap-htpy pr1-vertical-map-cocone-flat (right-square x)) ∙
            ( ap
              ( λ p → p ∙ inv refl)
              ( left-unit {p = ap (k' ∘ pr1-pr2) (right-square x)})) ∙
            ( right-unit {p = ap (k' ∘ pr1-pr2) (right-square x)})

          π₀ : fiber' hC (g (hA x)) → C'
          π₀ r = pr1 r

          π₁ : fiber' hC (hC (g' x)) → C'
          π₁ r = pr1 r

          ap-pr1-compute-tr-self-fiber'-compute-tr-fiber' :
            {y : C} (u : fiber' hC y) →
            ap pr1 (compute-tr-self-fiber' hC u) ＝
            ap pr1 (compute-tr-fiber' hC (pr2 u) u)
          ap-pr1-compute-tr-self-fiber'-compute-tr-fiber' (._ , refl) = refl

          pr1-tr-fiber'-htpy :
            (t : fiber' hC (g (hA x))) →
            pr1 (tr (fiber' hC) (back x) t) ＝ pr1 t
          pr1-tr-fiber'-htpy t =
            inv (ap pr1 (compute-tr-fiber' hC (back x) t))

          ap-pr1-inv-compute-tr-self-fiber'-htpy :
            {y : C} (u : fiber' hC y) →
            ap pr1 (inv-compute-tr-self-fiber' hC u) ＝
            inv (ap pr1 (compute-tr-fiber' hC (pr2 u) u))
          ap-pr1-inv-compute-tr-self-fiber'-htpy u =
            ( ap-inv pr1 (compute-tr-self-fiber' hC u)) ∙
            ( ap inv (ap-pr1-compute-tr-self-fiber'-compute-tr-fiber' u))

          ap-pr1-pr2-eq-pair-Σ :
            {y y' : C} (p : y ＝ y') (u : fiber' hC y) →
            ap pr1-pr2 (eq-pair-Σ p refl) ＝
            ap pr1 (compute-tr-fiber' hC p u)
          ap-pr1-pr2-eq-pair-Σ refl u = refl

          abstract
            ap-pr1-map-equiv-e-right :
              ap
                ( λ t →
                  pr1
                    ( map-equiv
                      ( e-right (g (hA x)))
                      ( t)))
                ( coherence-back-source x) ＝
              ap (k' ∘ pr1) (coherence-back-source x)
            ap-pr1-map-equiv-e-right =
              ( ap-htpy pr1-map-equiv-e-right (coherence-back-source x)) ∙
              ( ap
                ( λ p → p ∙ inv refl)
                ( left-unit {p = ap (k' ∘ pr1) (coherence-back-source x)})) ∙
              ( right-unit {p = ap (k' ∘ pr1) (coherence-back-source x)})

            ap-pr1-back-path :
              ap π₁ (back-path x) ＝
              inv (ap π₁ (compute-tr-fiber' hC (back x) (back-source x))) ∙
              ap π₀ (coherence-back-source x)
            ap-pr1-back-path =
              ( ap-concat π₁
                ( ap (tr (fiber' hC) (back x)) (coherence-back-source x))
                ( inv-compute-tr-self-fiber' hC (g' x , back x))) ∙
              ( ap
                ( λ p →
                  p ∙ ap π₁ (inv-compute-tr-self-fiber' hC (g' x , back x)))
                ( inv (ap-comp
                  {A = fiber' hC (g (hA x))}
                  {B = fiber' hC (hC (g' x))}
                  {C = C'}
                  π₁
                  ( tr (fiber' hC) (back x))
                  ( coherence-back-source x)))) ∙
              ( ap
                ( λ p →
                  p ∙ ap π₁ (inv-compute-tr-self-fiber' hC (g' x , back x)))
                ( ap-htpy pr1-tr-fiber'-htpy (coherence-back-source x))) ∙
              ( assoc
                ( pr1-tr-fiber'-htpy (back-source x) ∙
                  ap π₀ (coherence-back-source x))
                ( inv (pr1-tr-fiber'-htpy (g' x , back x)))
                ( ap π₁ (inv-compute-tr-self-fiber' hC (g' x , back x)))) ∙
              ( ap
                ( λ p →
                  pr1-tr-fiber'-htpy (back-source x) ∙
                  ap π₀ (coherence-back-source x) ∙
                  p)
                ( ap
                  ( λ p → inv (pr1-tr-fiber'-htpy (g' x , back x)) ∙ p)
                  ( ap-pr1-inv-compute-tr-self-fiber'-htpy (g' x , back x)))) ∙
              ( ap
                ( λ p →
                  pr1-tr-fiber'-htpy (back-source x) ∙
                  ap π₀ (coherence-back-source x) ∙
                  p)
                ( left-inv (pr1-tr-fiber'-htpy (g' x , back x)))) ∙
              ( right-unit)

          abstract
            ap-pr1-pr2-right-square :
              ap pr1-pr2 (right-square x) ＝
              ap pr1 (coherence-back-source x)
            ap-pr1-pr2-right-square =
              ( compute-ap-eq-pair-Σ pr1-pr2 (back x) (back-path x)) ∙
              ( ap
                ( λ p →
                  p ∙ ap (ev-pair pr1-pr2 (hC (g' x))) (back-path x))
                ( ap-pr1-pr2-eq-pair-Σ (back x) (back-source x))) ∙
              ( ap
                ( λ p →
                  ap π₁ (compute-tr-fiber' hC (back x) (back-source x)) ∙
                  p)
                ( ap-ev-pair-pr1-pr2)) ∙
              ( ap
                ( λ p →
                  ap π₁ (compute-tr-fiber' hC (back x) (back-source x)) ∙
                  p)
                ( ap-pr1-back-path)) ∙
              ( inv
                ( assoc
                  ( ap π₁ (compute-tr-fiber' hC (back x) (back-source x)))
                  ( pr1-tr-fiber'-htpy (back-source x))
                  ( ap π₀ (coherence-back-source x)))) ∙
              ( ap
                ( λ p → p ∙ ap π₀ (coherence-back-source x))
                ( right-inv
                  ( ap π₁ (compute-tr-fiber' hC (back x) (back-source x))))) ∙
              ( left-unit)
              where
              ev-pair-pr1-pr2 :
                ev-pair pr1-pr2 (hC (g' x)) ~ π₁
              ev-pair-pr1-pr2 t = refl

              ap-ev-pair-pr1-pr2 :
                ap (ev-pair pr1-pr2 (hC (g' x))) (back-path x) ＝
                ap π₁ (back-path x)
              ap-ev-pair-pr1-pr2 =
                ( ap-htpy ev-pair-pr1-pr2 (back-path x)) ∙
                ( ap
                  ( λ p → p ∙ inv refl)
                  ( left-unit {p = ap π₁ (back-path x)})) ∙
                ( right-unit {p = ap π₁ (back-path x)})

      abstract
        middle-third-top-flat-test :
          (x : A') →
          middle-term-top-flat x ∙
          ap pr1 (coherence-tr-front-right x) ＝
          third-term-top-flat x
        middle-third-top-flat-test x =
          ( middle-third-top-flat-target x) ∙
          ( third-term-top-flat-target x)

      abstract
        path-coherence-cocone-top-flat-is-top :
          (x : A') → path-coherence-cocone-top-flat x ＝ top x
        path-coherence-cocone-top-flat-is-top x =
          ( ap
            ( λ p → first-term-top-flat x ∙ p)
            ( inv (middle-third-top-flat-test x))) ∙
          ( inv
            ( assoc
              ( first-term-top-flat x)
              ( middle-term-top-flat x)
              ( ap pr1 (coherence-tr-front-right x)))) ∙
          ( ap
            ( λ p → p ∙ ap pr1 (coherence-tr-front-right x))
            ( first-middle-top-flat-test x)) ∙
          ( ap
            ( λ p → inv (ap pr1 (compute-tr-source-front x)) ∙ p)
            ( ap-pr1-coherence-tr-front-right x)) ∙
          ( inv
            ( assoc
              ( inv (ap pr1 (compute-tr-source-front x)))
              ( ap pr1 (compute-tr-source-front x) ∙
                ap pr1 (coherence-front-right x))
              ( ap pr1 (inv (compute-right x))))) ∙
          ( ap
            ( λ p → p ∙ ap pr1 (inv (compute-right x)))
            ( inv
              ( assoc
                ( inv (ap pr1 (compute-tr-source-front x)))
                ( ap pr1 (compute-tr-source-front x))
                ( ap pr1 (coherence-front-right x))))) ∙
          ( ap
            ( λ p → p ∙ ap pr1 (inv (compute-right x)))
            ( right-whisker-concat
              ( left-inv (ap pr1 (compute-tr-source-front x)))
              ( ap pr1 (coherence-front-right x)))) ∙
          ( ap
            ( λ p → p ∙ ap pr1 (inv (compute-right x)))
            ( left-unit {p = ap pr1 (coherence-front-right x)})) ∙
          ( ap
            ( λ p → ap pr1 (coherence-front-right x) ∙ p)
            ( ap-inv (pr1) (compute-right x))) ∙
          ( ap
            ( λ p → ap pr1 (coherence-front-right x) ∙ p)
            ( inv (ap-pr1-compute-right x))) ∙
          ( right-unit) ∙
          ( ap-pr1-coherence-front-right x)

      abstract
        coherence-cocone-top-flat :
          statement-coherence-htpy-cocone
            f'
            g'
            cocone-top-flat
            ( h' , k' , top)
            horizontal-cocone-top-flat
            vertical-cocone-top-flat
        coherence-cocone-top-flat x =
          right-unit ∙ path-coherence-cocone-top-flat-is-top x

        up-top :
          universal-property-pushout f' g' (h' , k' , top)
        up-top {l} =
          tr
            ( universal-property-pushout-Level l f' g')
            ( eq-htpy-cocone
              ( f')
              ( g')
              ( cocone-top-flat)
              ( h' , k' , top)
              ( horizontal-cocone-top-flat ,
                vertical-cocone-top-flat ,
                coherence-cocone-top-flat))
            ( up-top-flat)
```

## See also

- Mather's second cube theorem is the
  [unstraightened](foundation.type-duality.md) version of the
  [flattening lemma for pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md)
- The
  [descent property for pushouts](synthetic-homotopy-theory.descent-pushouts.md).

## External links

- [Mather's Second Cube Theorem](https://kerodon.net/tag/011H) on Kerodon
