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
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

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

We derive the theorem from the
[flattening lemma](synthetic-homotopy-theory.flattening-lemma-pushouts.md),
using a lot of coherence reasoning.

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

  equiv-left-mathers-second-cube-theorem :
    universal-property-pullback f hB (hA , f' , left) →
    (x : A) → fiber' hA x ≃ fiber' hB (f x)
  equiv-left-mathers-second-cube-theorem =
    fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
      f hB (hA , f' , left)

  equiv-front-mathers-second-cube-theorem :
    universal-property-pullback h hD (hB , h' , front) →
    (x : B) → fiber' hB x ≃ fiber' hD (h x)
  equiv-front-mathers-second-cube-theorem =
    fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
      h hD (hB , h' , front)

  equiv-right-mathers-second-cube-theorem :
    universal-property-pullback k hD (hC , k' , right) →
    (x : C) → fiber' hC x ≃ fiber' hD (k x)
  equiv-right-mathers-second-cube-theorem =
    fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
      k hD (hC , k' , right)

  map-left-mathers-second-cube-theorem :
    (pb-left : universal-property-pullback f hB (hA , f' , left)) →
    (x : A) → fiber' hA x → fiber' hB (f x)
  map-left-mathers-second-cube-theorem pb-left x =
    map-equiv (equiv-left-mathers-second-cube-theorem pb-left x)

  map-front-mathers-second-cube-theorem :
    (pb-front : universal-property-pullback h hD (hB , h' , front)) →
    (x : B) → fiber' hB x → fiber' hD (h x)
  map-front-mathers-second-cube-theorem pb-front x =
    map-equiv (equiv-front-mathers-second-cube-theorem pb-front x)

  map-right-mathers-second-cube-theorem :
    (pb-right : universal-property-pullback k hD (hC , k' , right)) →
    (x : C) → fiber' hC x → fiber' hD (k x)
  map-right-mathers-second-cube-theorem pb-right x =
    map-equiv (equiv-right-mathers-second-cube-theorem pb-right x)

  descent-data-pushout-mathers-second-cube-theorem :
    universal-property-pullback h hD (hB , h' , front) →
    universal-property-pullback k hD (hC , k' , right) →
    descent-data-pushout (make-span-diagram f g) (l2' ⊔ l2) (l3' ⊔ l3)
  descent-data-pushout-mathers-second-cube-theorem pb-front pb-right =
    ( fiber' hB ,
      fiber' hC ,
      ( λ s →
        ( inv-equiv (equiv-right-mathers-second-cube-theorem pb-right (g s))) ∘e
        ( equiv-tr (fiber' hD) (bottom s)) ∘e
        ( equiv-front-mathers-second-cube-theorem pb-front (f s))))

  equiv-descent-data-pushout-mathers-second-cube-theorem :
    ( pb-front : universal-property-pullback h hD (hB , h' , front)) →
    ( pb-right : universal-property-pullback k hD (hC , k' , right)) →
    equiv-descent-data-pushout
      ( descent-data-pushout-mathers-second-cube-theorem pb-front pb-right)
      ( descent-data-family-cocone-span-diagram (h , k , bottom) (fiber' hD))
  equiv-descent-data-pushout-mathers-second-cube-theorem pb-front pb-right =
    ( equiv-front-mathers-second-cube-theorem pb-front ,
      equiv-right-mathers-second-cube-theorem pb-right ,
      ( λ s t →
        is-section-map-inv-equiv
          ( equiv-right-mathers-second-cube-theorem pb-right (g s))
          ( tr
            ( fiber' hD)
            ( bottom s)
            ( map-front-mathers-second-cube-theorem pb-front (f s) t))))

  source-front-mathers-second-cube-theorem :
    universal-property-pullback h hD (hB , h' , front) →
    universal-property-pullback f hB (hA , f' , left) →
    (x : A') → fiber' hD (h (f (hA x)))
  source-front-mathers-second-cube-theorem pb-front pb-left x =
    map-front-mathers-second-cube-theorem pb-front
      ( f (hA x))
      ( map-left-mathers-second-cube-theorem pb-left (hA x) (x , refl))

  compute-source-front-mathers-second-cube-theorem :
    (pb-front : universal-property-pullback h hD (hB , h' , front)) →
    (pb-left : universal-property-pullback f hB (hA , f' , left)) →
    (x : A') →
    source-front-mathers-second-cube-theorem pb-front pb-left x ＝
    (h' (f' x) , ap h (left x) ∙ front (f' x))
  compute-source-front-mathers-second-cube-theorem pb-front pb-left x = refl

  abstract
    compute-tr-source-front-mathers-second-cube-theorem :
      (pb-front : universal-property-pullback h hD (hB , h' , front)) →
      (pb-left : universal-property-pullback f hB (hA , f' , left)) →
      (x : A') →
      tr
        ( fiber' hD)
        ( bottom (hA x))
        ( source-front-mathers-second-cube-theorem pb-front pb-left x) ＝
      ( h' (f' x) , inv (bottom (hA x)) ∙ (ap h (left x) ∙ front (f' x)))
    compute-tr-source-front-mathers-second-cube-theorem pb-front pb-left x =
      ( inv-compute-tr-fiber'
        hD
        ( bottom (hA x))
        ( source-front-mathers-second-cube-theorem pb-front pb-left x)) ∙
      ( ap
        ( tot (λ y → inv (bottom (hA x)) ∙_))
        ( compute-source-front-mathers-second-cube-theorem pb-front pb-left x))

  coherence-front-right-mathers-second-cube-theorem :
    (x : A') →
    ( h' (f' x) , inv (bottom (hA x)) ∙ (ap h (left x) ∙ front (f' x))) ＝
    (k' (g' x) , ap k (back x) ∙ right (g' x))
  coherence-front-right-mathers-second-cube-theorem x =
    eq-pair-Σ
      ( top x)
      ( ( inv (substitution-law-tr (k (g (hA x)) ＝_) hD (top x))) ∙
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

  abstract
    ap-pr1-coherence-front-right-mathers-second-cube-theorem :
      pr1 ·l coherence-front-right-mathers-second-cube-theorem ~ top
    ap-pr1-coherence-front-right-mathers-second-cube-theorem x =
      ap-pr1-eq-pair-Σ
        ( top x)
        ( ( inv (substitution-law-tr (k (g (hA x)) ＝_) hD (top x))) ∙
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

  compute-right-mathers-second-cube-theorem :
    (pb-right : universal-property-pullback k hD (hC , k' , right)) →
    (x : A') →
    map-right-mathers-second-cube-theorem pb-right (g (hA x)) (g' x , back x) ＝
    (k' (g' x) , ap k (back x) ∙ right (g' x))
  compute-right-mathers-second-cube-theorem pb-right x = refl

  abstract
    ap-pr1-compute-right-mathers-second-cube-theorem :
      (pb-right : universal-property-pullback k hD (hC , k' , right)) →
      (x : A') →
      ap pr1 (compute-right-mathers-second-cube-theorem pb-right x) ＝ refl
    ap-pr1-compute-right-mathers-second-cube-theorem pb-right = refl-htpy

  abstract
    coherence-tr-front-right-mathers-second-cube-theorem :
      (pb-front : universal-property-pullback h hD (hB , h' , front)) →
      (pb-right : universal-property-pullback k hD (hC , k' , right)) →
      (pb-left : universal-property-pullback f hB (hA , f' , left)) →
      (x : A') →
      tr
        ( fiber' hD)
        ( bottom (hA x))
        ( source-front-mathers-second-cube-theorem pb-front pb-left x) ＝
      map-right-mathers-second-cube-theorem pb-right (g (hA x)) (g' x , back x)
    coherence-tr-front-right-mathers-second-cube-theorem
      pb-front pb-right pb-left =
      ( compute-tr-source-front-mathers-second-cube-theorem pb-front pb-left) ∙h
      ( coherence-front-right-mathers-second-cube-theorem) ∙h
      ( inv-htpy (compute-right-mathers-second-cube-theorem pb-right))

  abstract
    ap-pr1-coherence-tr-front-right-mathers-second-cube-theorem :
      (pb-front : universal-property-pullback h hD (hB , h' , front)) →
      (pb-right : universal-property-pullback k hD (hC , k' , right)) →
      (pb-left : universal-property-pullback f hB (hA , f' , left)) →
      ( pr1) ·l
      ( coherence-tr-front-right-mathers-second-cube-theorem
        ( pb-front)
        ( pb-right)
        ( pb-left)) ~
      ( ( ( pr1) ·l
          ( compute-tr-source-front-mathers-second-cube-theorem
            ( pb-front)
            ( pb-left)) ∙h
          ( pr1 ·l coherence-front-right-mathers-second-cube-theorem)) ∙h
        ( pr1 ·l inv-htpy (compute-right-mathers-second-cube-theorem pb-right)))
    ap-pr1-coherence-tr-front-right-mathers-second-cube-theorem
      pb-front pb-right pb-left x =
      ( ap-concat
        ( pr1)
        ( compute-tr-source-front-mathers-second-cube-theorem pb-front
          ( pb-left)
          ( x) ∙
          ( coherence-front-right-mathers-second-cube-theorem x))
        ( inv (compute-right-mathers-second-cube-theorem pb-right x))) ∙
        ( ap
          ( _∙
            ap pr1 (inv (compute-right-mathers-second-cube-theorem pb-right x)))
          ( ap-concat
            ( pr1)
            ( compute-tr-source-front-mathers-second-cube-theorem pb-front
              ( pb-left)
              ( x))
            ( coherence-front-right-mathers-second-cube-theorem x)))

  back-source-mathers-second-cube-theorem :
    (pb-front : universal-property-pullback h hD (hB , h' , front)) →
    (pb-right : universal-property-pullback k hD (hC , k' , right)) →
    (pb-left : universal-property-pullback f hB (hA , f' , left)) →
    (x : A') → fiber' hC (g (hA x))
  back-source-mathers-second-cube-theorem pb-front pb-right pb-left x =
    map-family-descent-data-pushout
      ( descent-data-pushout-mathers-second-cube-theorem pb-front pb-right)
      ( hA x)
      ( pr2
        ( map-equiv
          ( ( equiv-tot (equiv-left-mathers-second-cube-theorem pb-left)) ∘e
            ( inv-equiv-total-fiber' hA))
          ( x)))

  abstract
    compute-back-source-mathers-second-cube-theorem :
      (pb-front : universal-property-pullback h hD (hB , h' , front)) →
      (pb-right : universal-property-pullback k hD (hC , k' , right)) →
      (pb-left : universal-property-pullback f hB (hA , f' , left)) →
      (x : A') →
      back-source-mathers-second-cube-theorem pb-front pb-right pb-left x ＝
      map-inv-equiv
        ( equiv-right-mathers-second-cube-theorem pb-right (g (hA x)))
        ( tr
          ( fiber' hD)
          ( bottom (hA x))
          ( source-front-mathers-second-cube-theorem pb-front pb-left x))
    compute-back-source-mathers-second-cube-theorem pb-front pb-right pb-left =
      refl-htpy

  abstract
    coherence-back-source-mathers-second-cube-theorem :
      (pb-front : universal-property-pullback h hD (hB , h' , front)) →
      (pb-right : universal-property-pullback k hD (hC , k' , right)) →
      (pb-left : universal-property-pullback f hB (hA , f' , left)) →
      (x : A') →
      back-source-mathers-second-cube-theorem pb-front pb-right pb-left x ＝
      (g' x , back x)
    coherence-back-source-mathers-second-cube-theorem
      pb-front pb-right pb-left x =
      ( compute-back-source-mathers-second-cube-theorem
        ( pb-front)
        ( pb-right)
        ( pb-left)
        ( x)) ∙
      ( ap
        ( map-inv-equiv
          ( equiv-right-mathers-second-cube-theorem pb-right (g (hA x))))
        ( coherence-tr-front-right-mathers-second-cube-theorem
          pb-front pb-right pb-left x)) ∙
      ( is-retraction-map-inv-equiv
        ( equiv-right-mathers-second-cube-theorem pb-right (g (hA x)))
        ( g' x , back x))

  abstract
    back-path-mathers-second-cube-theorem :
      (pb-front : universal-property-pullback h hD (hB , h' , front)) →
      (pb-right : universal-property-pullback k hD (hC , k' , right)) →
      (pb-left : universal-property-pullback f hB (hA , f' , left)) →
      (x : A') →
      tr
        ( fiber' hC)
        ( back x)
        ( back-source-mathers-second-cube-theorem pb-front pb-right pb-left x) ＝
      (g' x , refl)
    back-path-mathers-second-cube-theorem pb-front pb-right pb-left x =
      ( ap
        ( tr (fiber' hC) (back x))
        ( coherence-back-source-mathers-second-cube-theorem
          ( pb-front)
          ( pb-right)
          ( pb-left)
          ( x))) ∙
      ( inv-compute-tr-self-fiber' hC (g' x , back x))

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
      e-left = equiv-left-mathers-second-cube-theorem pb-left
      e-front = equiv-front-mathers-second-cube-theorem pb-front
      e-right = equiv-right-mathers-second-cube-theorem pb-right

      P = descent-data-pushout-mathers-second-cube-theorem pb-front pb-right

      e =
        equiv-descent-data-pushout-mathers-second-cube-theorem pb-front pb-right

      source-front =
        source-front-mathers-second-cube-theorem pb-front pb-left

      compute-source-front =
        compute-source-front-mathers-second-cube-theorem pb-front pb-left

      compute-tr-source-front =
        compute-tr-source-front-mathers-second-cube-theorem pb-front pb-left

      coherence-front-right = coherence-front-right-mathers-second-cube-theorem

      ap-pr1-coherence-front-right =
        ap-pr1-coherence-front-right-mathers-second-cube-theorem

      compute-right = compute-right-mathers-second-cube-theorem pb-right

      ap-pr1-compute-right =
        ap-pr1-compute-right-mathers-second-cube-theorem pb-right

      coherence-tr-front-right =
        coherence-tr-front-right-mathers-second-cube-theorem
          pb-front pb-right pb-left

      ap-pr1-coherence-tr-front-right =
        ap-pr1-coherence-tr-front-right-mathers-second-cube-theorem
          pb-front pb-right pb-left

      back-source =
        back-source-mathers-second-cube-theorem pb-front pb-right pb-left

      compute-back-source =
        compute-back-source-mathers-second-cube-theorem
          pb-front pb-right pb-left

      coherence-back-source =
        coherence-back-source-mathers-second-cube-theorem
          pb-front pb-right pb-left

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

      abstract
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
          ( D')
      cocone-flat =
        cocone-map
          ( vertical-map-span-flattening-descent-data-pushout P)
          ( horizontal-map-span-flattening-descent-data-pushout P)
          ( cocone-flat-Σ)
          ( map-equiv (equiv-total-fiber' hD))

      compute-vertical-map-cocone-flat :
        (t : Σ C (fiber' hC)) →
        pr1 (pr2 cocone-flat) t ＝
        pr1 (map-equiv (e-right (pr1 t)) (pr2 t))
      compute-vertical-map-cocone-flat t = refl

      abstract
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

      abstract
        left-square :
          coherence-square-maps
            ( f')
            ( map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))
            ( map-equiv (inv-equiv-total-fiber' hB))
            ( vertical-map-span-flattening-descent-data-pushout P)
        left-square x =
          eq-pair-Σ (left x) (inv-compute-tr-self-fiber' hB (f' x , left x))

      abstract
        back-path :
          (x : A') →
          tr
            ( fiber' hC)
            ( back x)
            ( back-source-mathers-second-cube-theorem pb-front
                pb-right pb-left x) ＝
          ( g' x , refl)
        back-path =
          back-path-mathers-second-cube-theorem pb-front pb-right pb-left

      abstract
        right-square :
          coherence-square-maps
            ( g')
            ( map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))
            ( map-equiv (inv-equiv-total-fiber' hC))
            ( horizontal-map-span-flattening-descent-data-pushout P)
        right-square x = eq-pair-Σ (back x) (back-path x)

      abstract
        first-term-top-flat :
          (x : A') → h' (f' x) ＝ k' (pr1 (back-source x))
        first-term-top-flat =
          ( pr1 cocone-flat ·l inv-htpy left-square) ∙h
          ( pr2 (pr2 cocone-flat) ·r
            map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))

      third-term-top-flat :
        (x : A') → k' (pr1 (back-source x)) ＝ k' (g' x)
      third-term-top-flat =
        ( pr1
          ( pr2 (cocone-comp-horizontal
            ( f')
            ( map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA))
            ( horizontal-map-span-flattening-descent-data-pushout P)
            ( map-equiv (inv-equiv-total-fiber' hB) ,
              vertical-map-span-flattening-descent-data-pushout P ,
              inv-htpy left-square)
            ( cocone-flat)))) ·l
        ( right-square)

      third-term-top-flat-compute :
        (x : A') →
        third-term-top-flat x ＝ ap (pr1 (pr2 cocone-flat)) (right-square x)
      third-term-top-flat-compute x = refl

      middle-term-top-flat :
        (x : A') →
        k' (pr1 (back-source x)) ＝
        pr1 (tr (fiber' hD) (bottom (hA x)) (source-front x))
      middle-term-top-flat x =
        ( ap
          ( λ t → pr1 (map-equiv (e-right (g (hA x))) t))
          ( compute-back-source x)) ∙
        ( ap pr1
          ( is-section-map-inv-equiv
            ( e-right (g (hA x)))
            ( tr (fiber' hD) (bottom (hA x)) (source-front x))))

      up-top-flat :
        universal-property-pushout
          ( f')
          ( g')
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

      abstract
        horizontal-cocone-top-flat :
          horizontal-map-cocone f' g' cocone-top-flat ~ h'
        horizontal-cocone-top-flat x = refl

      abstract
        vertical-cocone-top-flat :
          vertical-map-cocone f' g' cocone-top-flat ~ k'
        vertical-cocone-top-flat x = refl

      path-coherence-cocone-top-flat : (x : A') → h' (f' x) ＝ k' (g' x)
      path-coherence-cocone-top-flat x =
        first-term-top-flat x ∙ third-term-top-flat x

      module _ (x : A') where

        eR-middle-third-top-flat-target :
          fiber' hC (g (hA x)) ≃ fiber' hD (k (g (hA x)))
        eR-middle-third-top-flat-target = e-right (g (hA x))

        u-middle-third-top-flat-target : fiber' hD (k (g (hA x)))
        u-middle-third-top-flat-target =
          tr (fiber' hD) (bottom (hA x)) (source-front x)

        v-middle-third-top-flat-target : fiber' hD (k (g (hA x)))
        v-middle-third-top-flat-target =
          map-equiv eR-middle-third-top-flat-target (g' x , back x)

        F-middle-third-top-flat-target : fiber' hC (g (hA x)) → D'
        F-middle-third-top-flat-target t =
          pr1 (map-equiv eR-middle-third-top-flat-target t)

        π-middle-third-top-flat-target : fiber' hD (k (g (hA x))) → D'
        π-middle-third-top-flat-target = pr1

        abstract
          H-middle-third-top-flat-target :
            ( λ t →
              pr1
                ( map-equiv
                  ( e-right (g (hA x)))
                  ( map-inv-equiv eR-middle-third-top-flat-target t))) ~
            ( π-middle-third-top-flat-target)
          H-middle-third-top-flat-target t =
            ap
              π-middle-third-top-flat-target
              (is-section-map-inv-equiv eR-middle-third-top-flat-target t)

        abstract
          section-to-retraction-middle-third-top-flat-target :
            ap
              ( π-middle-third-top-flat-target)
              ( is-section-map-inv-equiv
                ( eR-middle-third-top-flat-target)
                ( v-middle-third-top-flat-target)) ＝
            ap
              ( F-middle-third-top-flat-target)
              ( is-retraction-map-inv-equiv
                ( eR-middle-third-top-flat-target)
                ( g' x , back x))
          section-to-retraction-middle-third-top-flat-target =
            ( ap
              (ap π-middle-third-top-flat-target)
              ( coherence-map-inv-equiv
                eR-middle-third-top-flat-target
                (g' x , back x))) ∙
            ( inv
              ( ap-comp
                ( π-middle-third-top-flat-target)
                ( map-equiv eR-middle-third-top-flat-target)
                ( is-retraction-map-inv-equiv
                  eR-middle-third-top-flat-target
                  (g' x , back x))))

        abstract
          middle-third-top-flat-target :
            middle-term-top-flat x ∙
            ap pr1 (coherence-tr-front-right x) ＝
            ap
              ( λ t → pr1 (map-equiv (e-right (g (hA x))) t))
              ( coherence-back-source x)
          middle-third-top-flat-target =
            ( assoc
              ( ap F-middle-third-top-flat-target (compute-back-source x))
              ( ap
                π-middle-third-top-flat-target
                ( is-section-map-inv-equiv
                  eR-middle-third-top-flat-target
                  u-middle-third-top-flat-target))
              ( ap
                ( π-middle-third-top-flat-target)
                ( coherence-tr-front-right x))) ∙
            ( ap
              ( ap F-middle-third-top-flat-target (compute-back-source x) ∙_)
              ( nat-htpy
                H-middle-third-top-flat-target
                (coherence-tr-front-right x))) ∙
            ( inv
              ( assoc
                ( ap F-middle-third-top-flat-target (compute-back-source x))
                ( ap
                  ( F-middle-third-top-flat-target ∘
                    map-inv-equiv eR-middle-third-top-flat-target)
                  ( coherence-tr-front-right x))
                ( ap
                  π-middle-third-top-flat-target
                  ( is-section-map-inv-equiv
                    eR-middle-third-top-flat-target
                    v-middle-third-top-flat-target)))) ∙
            ( ap
              ( λ q →
                ( ( ap
                    ( F-middle-third-top-flat-target)
                    ( compute-back-source x)) ∙
                  ( q)) ∙
                ap
                  ( π-middle-third-top-flat-target)
                  ( is-section-map-inv-equiv
                    ( eR-middle-third-top-flat-target)
                    ( v-middle-third-top-flat-target)))
              ( ap-comp
                ( F-middle-third-top-flat-target)
                ( map-inv-equiv eR-middle-third-top-flat-target)
                ( coherence-tr-front-right x))) ∙
            ( ap
              ( _∙
                ap
                  ( π-middle-third-top-flat-target)
                  ( is-section-map-inv-equiv
                    ( eR-middle-third-top-flat-target)
                    ( v-middle-third-top-flat-target)))
              ( inv
                ( ap-concat
                  ( F-middle-third-top-flat-target)
                  ( compute-back-source x)
                  ( ap
                    ( map-inv-equiv eR-middle-third-top-flat-target)
                    ( coherence-tr-front-right x))))) ∙
            ( ap
              ( ap
                  ( F-middle-third-top-flat-target)
                  ( compute-back-source x ∙
                    ap
                      (map-inv-equiv eR-middle-third-top-flat-target)
                      (coherence-tr-front-right x)) ∙_)
              ( section-to-retraction-middle-third-top-flat-target)) ∙
            ( inv
              ( ap-concat
                ( F-middle-third-top-flat-target)
                ( compute-back-source x ∙
                  ap
                    ( map-inv-equiv eR-middle-third-top-flat-target)
                    ( coherence-tr-front-right x))
                ( is-retraction-map-inv-equiv
                  ( eR-middle-third-top-flat-target)
                  ( g' x , back x))))

      module _ (x : A') where

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

        abstract
          ap-pr1-compute-tr-self-fiber'-compute-tr-fiber'-B :
            {y : B} (v : fiber' hB y) →
            ap pr1 (compute-tr-self-fiber' hB v) ＝
            ap pr1 (compute-tr-fiber' hB (pr2 v) v)
          ap-pr1-compute-tr-self-fiber'-compute-tr-fiber'-B (._ , refl) = refl

        abstract
          ap-pr1-inv-compute-tr-self-fiber'-htpy-B :
            {y : B} (v : fiber' hB y) →
            ap pr1 (inv-compute-tr-self-fiber' hB v) ＝
            inv (ap pr1 (compute-tr-fiber' hB (pr2 v) v))
          ap-pr1-inv-compute-tr-self-fiber'-htpy-B v =
            ( ap-inv pr1 (compute-tr-self-fiber' hB v)) ∙
            ( ap inv (ap-pr1-compute-tr-self-fiber'-compute-tr-fiber'-B v))

        abstract
          ap-pr1-pr2-eq-pair-Σ-B :
            {y y' : B} (p : y ＝ y') (v : fiber' hB y) →
            ap pr1-pr2-B (eq-pair-Σ p refl) ＝
            ap pr1 (compute-tr-fiber' hB p v)
          ap-pr1-pr2-eq-pair-Σ-B refl v = refl

        abstract
          ap-pr1-pr2-left-square :
            ap pr1-pr2-B (left-square x) ＝ refl
          ap-pr1-pr2-left-square =
            ( compute-ap-eq-pair-Σ
              ( pr1-pr2-B)
              ( left x)
              ( inv-compute-tr-self-fiber' hB (f' x , left x))) ∙
            ( ap
              ( _∙ ap pr1 (inv-compute-tr-self-fiber' hB (f' x , left x)))
              ( ap-pr1-pr2-eq-pair-Σ-B (left x) (f' x , left x))) ∙
            ( ap
              ( ap pr1 (compute-tr-fiber' hB (left x) (f' x , left x)) ∙_)
              ( ap-pr1-inv-compute-tr-self-fiber'-htpy-B (f' x , left x))) ∙
            ( right-inv
              ( ap pr1 (compute-tr-fiber' hB (left x) (f' x , left x))))

        abstract
          ap-pr1-cocone-flat-left-square :
            ap (pr1 cocone-flat) (left-square x) ＝ refl
          ap-pr1-cocone-flat-left-square =
            ( ap-comp h' pr1-pr2-B (left-square x)) ∙
            ( ap (ap h') ap-pr1-pr2-left-square) ∙
            ( ap-refl h' (f' x))

        abstract
          ap-pr1-cocone-flat-inv-left-square :
            ap (pr1 cocone-flat) (inv (left-square x)) ＝ refl
          ap-pr1-cocone-flat-inv-left-square =
            ( ap-inv (pr1 cocone-flat) (left-square x)) ∙
            ( ap inv ap-pr1-cocone-flat-left-square)

        abstract
          ap-pr1-pr2-eq-pair-Σ-D :
            {y y' : D} (p : y ＝ y') (v : fiber' hD y) →
            ap pr1-pr2-D (eq-pair-Σ p refl) ＝
            ap pr1 (compute-tr-fiber' hD p v)
          ap-pr1-pr2-eq-pair-Σ-D refl v = refl

        abstract
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
              ( _∙ ap pr1 (inv (is-section-map-inv-equiv eR u)))
              ( ap-pr1-pr2-eq-pair-Σ-D
                ( bottom (hA x))
                ( source-front x)))

        abstract
          cancel-is-section :
            ap pr1 (inv (is-section-map-inv-equiv eR u)) ∙
            middle-term-top-flat x ＝
            refl
          cancel-is-section =
            ( ap
              ( _∙ ap pr1 (is-section-map-inv-equiv eR u))
              ( ap-inv pr1 (is-section-map-inv-equiv eR u))) ∙
            ( left-inv (ap pr1 (is-section-map-inv-equiv eR u)))

        abstract
          ap-pr1-ap-tot-compute-source-front :
            ap pr1
              ( ap
                ( tot (λ y → inv (bottom (hA x)) ∙_))
                ( compute-source-front x)) ＝
            refl
          ap-pr1-ap-tot-compute-source-front =
            ( inv
              ( ap-comp
                ( pr1)
                ( tot (λ y → inv (bottom (hA x)) ∙_))
                ( compute-source-front x))) ∙
            ( ap-refl
              ( pr1 ∘ tot (λ y → inv (bottom (hA x)) ∙_))
              ( source-front x))

        abstract
          ap-pr1-compute-tr-source-front :
            ap pr1 (compute-tr-source-front x) ＝
            ap pr1 (inv-compute-tr-fiber' hD (bottom (hA x)) (source-front x))
          ap-pr1-compute-tr-source-front =
            ( ap-concat
              ( pr1)
              ( inv-compute-tr-fiber' hD (bottom (hA x)) (source-front x))
              ( ap
                ( tot (λ y → inv (bottom (hA x)) ∙_))
                ( compute-source-front x))) ∙
            ( ap
              ( ap
                ( pr1)
                ( inv-compute-tr-fiber' hD (bottom (hA x)) (source-front x)) ∙_)
              ( ap-pr1-ap-tot-compute-source-front)) ∙
            ( right-unit)

        abstract
          inv-ap-pr1-inv-compute-tr-fiber' :
            inv
              ( ap
                ( pr1)
                ( inv-compute-tr-fiber' hD (bottom (hA x)) (source-front x))) ＝
            ap pr1 (compute-tr-fiber' hD (bottom (hA x)) (source-front x))
          inv-ap-pr1-inv-compute-tr-fiber' =
            ( ap inv
              ( ap-inv pr1
                ( compute-tr-fiber' hD (bottom (hA x)) (source-front x)))) ∙
            ( inv-inv
              ( ap pr1
                ( compute-tr-fiber' hD (bottom (hA x)) (source-front x))))

        abstract
          inv-ap-pr1-compute-tr-source-front :
            ap pr1 (compute-tr-fiber' hD (bottom (hA x)) (source-front x)) ＝
            inv (ap pr1 (compute-tr-source-front x))
          inv-ap-pr1-compute-tr-source-front =
            ( inv inv-ap-pr1-inv-compute-tr-fiber') ∙
            ( inv (ap inv ap-pr1-compute-tr-source-front))

        abstract
          first-middle-top-flat :
            first-term-top-flat x ∙ middle-term-top-flat x ＝
            inv (ap pr1 (compute-tr-source-front x))
          first-middle-top-flat =
            ( assoc (ap (pr1 cocone-flat) (inv (left-square x))) q r) ∙
            ( ap (_∙ (q ∙ r)) ap-pr1-cocone-flat-inv-left-square) ∙
            ( ap (_∙ r) coherence-top-flat) ∙
            ( assoc
              ( ap pr1 (compute-tr-fiber' hD (bottom (hA x)) (source-front x)))
              ( ap pr1 (inv (is-section-map-inv-equiv eR u)))
              ( r)) ∙
            ( ap
              ( ap
                ( pr1)
                ( compute-tr-fiber' hD (bottom (hA x)) (source-front x)) ∙_)
              ( cancel-is-section)) ∙
            ( right-unit) ∙
            ( inv-ap-pr1-compute-tr-source-front)

      third-term-top-flat-target :
        (x : A') →
        ap
          ( λ t → pr1 (map-equiv (e-right (g (hA x))) t))
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
          pr1-map-equiv-e-right :
            {c : C} (t : fiber' hC c) →
            pr1 (map-equiv (e-right c) t) ＝ k' (pr1 t)
          pr1-map-equiv-e-right t = refl

          pr1-pr2 : Σ C (fiber' hC) → C'
          pr1-pr2 t = pr1 (pr2 t)

          abstract
            pr1-vertical-map-cocone-flat :
              (t : Σ C (fiber' hC)) →
              pr1 (pr2 cocone-flat) t ＝ k' (pr1 (pr2 t))
            pr1-vertical-map-cocone-flat t =
              pr1-map-equiv-e-right (pr2 t)

          abstract
            ap-pr1-vertical-map-cocone-flat :
              ap (pr1 (pr2 cocone-flat)) (right-square x) ＝
              ap (k' ∘ pr1-pr2) (right-square x)
            ap-pr1-vertical-map-cocone-flat =
              ( ap-htpy pr1-vertical-map-cocone-flat (right-square x)) ∙
              ( right-unit {p = ap (k' ∘ pr1-pr2) (right-square x)})

          π₀ : fiber' hC (g (hA x)) → C'
          π₀ r = pr1 r

          π₁ : fiber' hC (hC (g' x)) → C'
          π₁ r = pr1 r

          abstract
            ap-pr1-compute-tr-self-fiber'-compute-tr-fiber' :
              {y : C} (u : fiber' hC y) →
              ap pr1 (compute-tr-self-fiber' hC u) ＝
              ap pr1 (compute-tr-fiber' hC (pr2 u) u)
            ap-pr1-compute-tr-self-fiber'-compute-tr-fiber' (._ , refl) = refl

          abstract
            pr1-tr-fiber'-htpy :
              (t : fiber' hC (g (hA x))) →
              pr1 (tr (fiber' hC) (back x) t) ＝ pr1 t
            pr1-tr-fiber'-htpy t =
              inv (ap pr1 (compute-tr-fiber' hC (back x) t))

          abstract
            ap-pr1-inv-compute-tr-self-fiber'-htpy :
              {y : C} (u : fiber' hC y) →
              ap pr1 (inv-compute-tr-self-fiber' hC u) ＝
              inv (ap pr1 (compute-tr-fiber' hC (pr2 u) u))
            ap-pr1-inv-compute-tr-self-fiber'-htpy u =
              ( ap-inv pr1 (compute-tr-self-fiber' hC u)) ∙
              ( ap inv (ap-pr1-compute-tr-self-fiber'-compute-tr-fiber' u))

          abstract
            ap-pr1-pr2-eq-pair-Σ :
              {y y' : C} (p : y ＝ y') (u : fiber' hC y) →
              ap pr1-pr2 (eq-pair-Σ p refl) ＝
              ap pr1 (compute-tr-fiber' hC p u)
            ap-pr1-pr2-eq-pair-Σ refl u = refl

          abstract
            ap-pr1-map-equiv-e-right :
              ap
                ( λ t → pr1 (map-equiv (e-right (g (hA x))) t))
                ( coherence-back-source x) ＝
              ap (k' ∘ pr1) (coherence-back-source x)
            ap-pr1-map-equiv-e-right =
              ( ap-htpy pr1-map-equiv-e-right (coherence-back-source x)) ∙
              ( right-unit {p = ap (k' ∘ pr1) (coherence-back-source x)})

          abstract
            ap-pr1-back-path :
              ap π₁ (back-path x) ＝
              inv (ap π₁ (compute-tr-fiber' hC (back x) (back-source x))) ∙
              ap π₀ (coherence-back-source x)
            ap-pr1-back-path =
              ( ap-concat π₁
                ( ap (tr (fiber' hC) (back x)) (coherence-back-source x))
                ( inv-compute-tr-self-fiber' hC (g' x , back x))) ∙
              ( ap
                ( _∙ ap π₁ (inv-compute-tr-self-fiber' hC (g' x , back x)))
                ( inv
                  ( ap-comp
                    {A = fiber' hC (g (hA x))}
                    {B = fiber' hC (hC (g' x))}
                    {C = C'}
                    ( π₁)
                    ( tr (fiber' hC) (back x))
                    ( coherence-back-source x)))) ∙
              ( ap
                ( _∙ ap π₁ (inv-compute-tr-self-fiber' hC (g' x , back x)))
                ( ap-htpy pr1-tr-fiber'-htpy (coherence-back-source x))) ∙
              ( assoc
                ( ( pr1-tr-fiber'-htpy (back-source x)) ∙
                  ( ap π₀ (coherence-back-source x)))
                ( inv (pr1-tr-fiber'-htpy (g' x , back x)))
                ( ap π₁ (inv-compute-tr-self-fiber' hC (g' x , back x)))) ∙
              ( ap
                ( ( ( pr1-tr-fiber'-htpy (back-source x)) ∙
                    ( ap π₀ (coherence-back-source x))) ∙_)
                ( ap
                  ( inv (pr1-tr-fiber'-htpy (g' x , back x)) ∙_)
                  ( ap-pr1-inv-compute-tr-self-fiber'-htpy (g' x , back x)))) ∙
              ( ap
                ( ( ( pr1-tr-fiber'-htpy (back-source x)) ∙
                    ( ap π₀ (coherence-back-source x))) ∙_)
                ( left-inv (pr1-tr-fiber'-htpy (g' x , back x)))) ∙
              ( right-unit)

          abstract
            ap-pr1-pr2-right-square :
              ap pr1-pr2 (right-square x) ＝
              ap pr1 (coherence-back-source x)
            ap-pr1-pr2-right-square =
              ( compute-ap-eq-pair-Σ pr1-pr2 (back x) (back-path x)) ∙
              ( ap
                ( _∙ ap (ev-pair pr1-pr2 (hC (g' x))) (back-path x))
                ( ap-pr1-pr2-eq-pair-Σ (back x) (back-source x))) ∙
              ( ap
                ( ap π₁ (compute-tr-fiber' hC (back x) (back-source x)) ∙_)
                ( ap-ev-pair-pr1-pr2)) ∙
              ( ap
                ( ap π₁ (compute-tr-fiber' hC (back x) (back-source x)) ∙_)
                ( ap-pr1-back-path)) ∙
              ( inv
                ( assoc
                  ( ap π₁ (compute-tr-fiber' hC (back x) (back-source x)))
                  ( pr1-tr-fiber'-htpy (back-source x))
                  ( ap π₀ (coherence-back-source x)))) ∙
              ( ap
                ( _∙ ap π₀ (coherence-back-source x))
                ( right-inv
                  ( ap π₁ (compute-tr-fiber' hC (back x) (back-source x)))))
              where

              ev-pair-pr1-pr2 :
                ev-pair pr1-pr2 (hC (g' x)) ~ π₁
              ev-pair-pr1-pr2 t = refl

              ap-ev-pair-pr1-pr2 :
                ap (ev-pair pr1-pr2 (hC (g' x))) (back-path x) ＝
                ap π₁ (back-path x)
              ap-ev-pair-pr1-pr2 =
                ( ap-htpy ev-pair-pr1-pr2 (back-path x)) ∙
                ( right-unit {p = ap π₁ (back-path x)})

      abstract
        middle-third-top-flat-test :
          (x : A') →
          middle-term-top-flat x ∙
          ap pr1 (coherence-tr-front-right x) ＝
          third-term-top-flat x
        middle-third-top-flat-test =
          middle-third-top-flat-target ∙h third-term-top-flat-target

      abstract
        path-coherence-cocone-top-flat-is-top :
          path-coherence-cocone-top-flat ~ top
        path-coherence-cocone-top-flat-is-top x =
          ( ap
            ( first-term-top-flat x ∙_)
            ( inv (middle-third-top-flat-test x))) ∙
          ( inv
            ( assoc
              ( first-term-top-flat x)
              ( middle-term-top-flat x)
              ( ap pr1 (coherence-tr-front-right x)))) ∙
          ( ap
            ( _∙ ap pr1 (coherence-tr-front-right x))
            ( first-middle-top-flat x)) ∙
          ( ap
            ( inv (ap pr1 (compute-tr-source-front x)) ∙_)
            ( ap-pr1-coherence-tr-front-right x)) ∙
          ( inv
            ( assoc
              ( inv (ap pr1 (compute-tr-source-front x)))
              ( ( ap pr1 (compute-tr-source-front x)) ∙
                ( ap pr1 (coherence-front-right x)))
              ( ap pr1 (inv (compute-right x))))) ∙
          ( ap
            ( _∙ ap pr1 (inv (compute-right x)))
            ( inv
              ( assoc
                ( inv (ap pr1 (compute-tr-source-front x)))
                ( ap pr1 (compute-tr-source-front x))
                ( ap pr1 (coherence-front-right x))))) ∙
          ( ap
            ( _∙ ap pr1 (inv (compute-right x)))
            ( right-whisker-concat
              ( left-inv (ap pr1 (compute-tr-source-front x)))
              ( ap pr1 (coherence-front-right x)))) ∙
          ( ap
            ( ap pr1 (coherence-front-right x) ∙_)
            ( ap-inv pr1 (compute-right x))) ∙
          ( ap
            ( ap pr1 (coherence-front-right x) ∙_)
            ( inv (ap-pr1-compute-right x))) ∙
          ( right-unit) ∙
          ( ap-pr1-coherence-front-right x)

      abstract
        coherence-cocone-top-flat :
          statement-coherence-htpy-cocone
            ( f')
            ( g')
            ( cocone-top-flat)
            ( h' , k' , top)
            ( horizontal-cocone-top-flat)
            ( vertical-cocone-top-flat)
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
