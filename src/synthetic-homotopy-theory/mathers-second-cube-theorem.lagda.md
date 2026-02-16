# Mather's second cube theorem

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.mathers-second-cube-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.action-on-identifications-ternary-functions
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

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.equifibered-span-diagrams
open import synthetic-homotopy-theory.equivalences-equifibered-span-diagrams
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
  |⌟\                 |⌟\
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

We assume a (fully universe-polymorphic) commuting cube of maps.

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
```

First we turn the pullback assumptions on the individual vertical faces into
fiberwise equivalences to construct an equifibered span diagram.

```agda
  fiberwise-equiv-left-mathers-cube :
    universal-property-pullback f hB (hA , f' , left) →
    (a : A) → fiber' hA a ≃ fiber' hB (f a)
  fiberwise-equiv-left-mathers-cube pb-left =
    fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
      f hB (hA , f' , left) pb-left

  fiberwise-map-left-mathers-cube :
    universal-property-pullback f hB (hA , f' , left) →
    (a : A) → fiber' hA a → fiber' hB (f a)
  fiberwise-map-left-mathers-cube pb-left =
    map-equiv ∘ fiberwise-equiv-left-mathers-cube pb-left

  fiberwise-equiv-back-mathers-cube :
    universal-property-pullback g hC (hA , g' , back) →
    (a : A) → fiber' hA a ≃ fiber' hC (g a)
  fiberwise-equiv-back-mathers-cube pb-back =
    fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
      g hC (hA , g' , back) pb-back

  fiberwise-map-back-mathers-cube :
    universal-property-pullback g hC (hA , g' , back) →
    (a : A) → fiber' hA a → fiber' hC (g a)
  fiberwise-map-back-mathers-cube pb-back =
    map-equiv ∘ fiberwise-equiv-back-mathers-cube pb-back

  fiberwise-equiv-front-mathers-cube :
    universal-property-pullback h hD (hB , h' , front) →
    (b : B) → fiber' hB b ≃ fiber' hD (h b)
  fiberwise-equiv-front-mathers-cube pb-front =
    fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
      h hD (hB , h' , front) pb-front

  fiberwise-map-front-mathers-cube :
    universal-property-pullback h hD (hB , h' , front) →
    (b : B) → fiber' hB b → fiber' hD (h b)
  fiberwise-map-front-mathers-cube pb-front =
    map-equiv ∘ fiberwise-equiv-front-mathers-cube pb-front

  fiberwise-equiv-right-mathers-cube :
    universal-property-pullback k hD (hC , k' , right) →
    (c : C) → fiber' hC c ≃ fiber' hD (k c)
  fiberwise-equiv-right-mathers-cube pb-right =
    fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
      k hD (hC , k' , right) pb-right

  fiberwise-map-right-mathers-cube :
    universal-property-pullback k hD (hC , k' , right) →
    (c : C) → fiber' hC c → fiber' hD (k c)
  fiberwise-map-right-mathers-cube pb-right =
    map-equiv ∘ fiberwise-equiv-right-mathers-cube pb-right

  equifibered-span-diagram-mathers-cube :
    universal-property-pullback f hB (hA , f' , left) →
    universal-property-pullback g hC (hA , g' , back) →
    equifibered-span-diagram
      ( make-span-diagram f g)
      ( l2' ⊔ l2)
      ( l3' ⊔ l3)
      ( l1' ⊔ l1)
  equifibered-span-diagram-mathers-cube pb-left pb-back =
    ( fiber' hB ,
      fiber' hC ,
      fiber' hA ,
      fiberwise-equiv-left-mathers-cube pb-left ,
      fiberwise-equiv-back-mathers-cube pb-back)

  back-left-mathers-cube :
    (pb-left : universal-property-pullback f hB (hA , f' , left))
    (pb-back : universal-property-pullback g hC (hA , g' , back)) →
    coherence-square-maps
      ( f')
      ( map-equiv (inv-equiv-total-fiber' hA))
      ( map-equiv (inv-equiv-total-fiber' hB))
      ( vertical-map-span-flattening-equifibered-span-diagram
        ( equifibered-span-diagram-mathers-cube pb-left pb-back))
  back-left-mathers-cube pb-left pb-back x =
    eq-pair-Σ (left x) (inv-compute-tr-self-fiber' hB (f' x , left x))

  back-right-mathers-cube :
    (pb-left : universal-property-pullback f hB (hA , f' , left))
    (pb-back : universal-property-pullback g hC (hA , g' , back)) →
    coherence-square-maps
      ( g')
      ( map-equiv (inv-equiv-total-fiber' hA))
      ( map-equiv (inv-equiv-total-fiber' hC))
      ( horizontal-map-span-flattening-equifibered-span-diagram
        ( equifibered-span-diagram-mathers-cube pb-left pb-back))
  back-right-mathers-cube pb-left pb-back x =
    eq-pair-Σ (back x) (inv-compute-tr-self-fiber' hC (g' x , back x))
```

Let us now assume that the four vertical faces are pullback squares.

```agda
  module _
    (pb-front : universal-property-pullback h hD (hB , h' , front))
    (pb-right : universal-property-pullback k hD (hC , k' , right))
    (pb-left : universal-property-pullback f hB (hA , f' , left))
    (pb-back : universal-property-pullback g hC (hA , g' , back))
    where

    coherence-left-equiv-equifibered-span-diagram-mathers-second-cube-theorem :
      (a : A) →
      coherence-square-maps
        ( ( fiberwise-map-front-mathers-cube pb-front (f a)) ∘
          ( fiberwise-map-left-mathers-cube pb-left a))
        ( map-left-family-equifibered-span-diagram
          ( equifibered-span-diagram-mathers-cube pb-left pb-back)
          ( a))
        ( map-left-family-equifibered-span-diagram
          ( equifibered-span-diagram-family-cocone-span-diagram
            ( h , k , bottom)
            ( fiber' hD))
          ( a))
        ( fiberwise-map-front-mathers-cube pb-front (f a))
    coherence-left-equiv-equifibered-span-diagram-mathers-second-cube-theorem
      a t =
      refl

    coherence-right-equiv-equifibered-span-diagram-mathers-second-cube-theorem :
      (a : A) →
      coherence-square-maps
        ( ( fiberwise-map-front-mathers-cube pb-front (f a)) ∘
          ( fiberwise-map-left-mathers-cube pb-left a))
        ( map-right-family-equifibered-span-diagram
          ( equifibered-span-diagram-mathers-cube pb-left pb-back)
          ( a))
        ( map-right-family-equifibered-span-diagram
          ( equifibered-span-diagram-family-cocone-span-diagram
            ( h , k , bottom)
            ( fiber' hD))
          ( a))
        ( fiberwise-map-right-mathers-cube pb-right (g a))
    coherence-right-equiv-equifibered-span-diagram-mathers-second-cube-theorem
      .(hA x)
      ( x , refl) =
      ( eq-Eq-fiber'
        ( hD)
        ( k (g (hA x)))
        ( inv (top x))
        ( ( double-transpose-eq-concat
            ( bottom (hA x))
            ( ap h (left x) ∙ front (f' x))
            ( ap k (back x) ∙ right (g' x))
            ( ap hD (top x))
            ( c x)) ∙
          ( ap
            ( (ap k (back x) ∙ right (g' x)) ∙_)
            ( inv-ap-inv hD (top x))))) ∙
      ( compute-tr-fiber'
        ( hD)
        ( bottom (hA x))
        ( ( ( fiberwise-map-front-mathers-cube pb-front (f (hA x))) ∘
            ( fiberwise-map-left-mathers-cube pb-left (hA x)))
          ( x , refl)))

    equiv-equifibered-span-diagram-mathers-second-cube-theorem :
      equiv-equifibered-span-diagram
        ( equifibered-span-diagram-mathers-cube pb-left pb-back)
        ( equifibered-span-diagram-family-cocone-span-diagram
          ( h , k , bottom)
          ( fiber' hD))
    equiv-equifibered-span-diagram-mathers-second-cube-theorem =
      ( fiberwise-equiv-front-mathers-cube pb-front ,
        fiberwise-equiv-right-mathers-cube pb-right ,
        ( λ a →
          ( fiberwise-equiv-front-mathers-cube pb-front (f a)) ∘e
          ( fiberwise-equiv-left-mathers-cube pb-left a)) ,
        coherence-left-equiv-equifibered-span-diagram-mathers-second-cube-theorem ,
        coherence-right-equiv-equifibered-span-diagram-mathers-second-cube-theorem)

    cocone-postcompose-mathers-second-cube-theorem :
      cocone
        ( vertical-map-span-flattening-equifibered-span-diagram
          ( equifibered-span-diagram-mathers-cube pb-left pb-back))
        ( horizontal-map-span-flattening-equifibered-span-diagram
          ( equifibered-span-diagram-mathers-cube pb-left pb-back))
        ( D')
    cocone-postcompose-mathers-second-cube-theorem =
      cocone-map _ _
        ( cocone-flattening-equifibered-span-diagram f g
          ( h , k , bottom)
          ( equifibered-span-diagram-mathers-cube pb-left pb-back)
          ( fiber' hD)
          ( equiv-equifibered-span-diagram-mathers-second-cube-theorem))
        ( map-equiv-total-fiber' hD)
```

Using that equivalence, we construct a postcomposed cocone in `D'` and use the
flattening lemma for equifibered span diagrams to show this is a pushout.

```agda
    universal-property-pushout-cocone-postcompose-mathers-second-cube-theorem :
      (po-bottom : universal-property-pushout f g (h , k , bottom)) →
      universal-property-pushout
        ( vertical-map-span-flattening-equifibered-span-diagram
          ( equifibered-span-diagram-mathers-cube pb-left pb-back))
        ( horizontal-map-span-flattening-equifibered-span-diagram
          ( equifibered-span-diagram-mathers-cube pb-left pb-back))
        ( cocone-postcompose-mathers-second-cube-theorem)
    universal-property-pushout-cocone-postcompose-mathers-second-cube-theorem
      po-bottom =
      up-pushout-up-pushout-is-equiv _ _ _ _
        ( map-equiv-total-fiber' hD)
        ( refl-htpy-cocone _ _ _)
        ( is-equiv-map-equiv-total-fiber' hD)
        ( flattening-lemma-equifibered-span-diagram f g
          ( h , k , bottom)
          ( equifibered-span-diagram-mathers-cube pb-left pb-back)
          ( fiber' hD)
          ( equiv-equifibered-span-diagram-mathers-second-cube-theorem)
          ( po-bottom))

    cocone-span-extension-mathers-second-cube-theorem :
      cocone f' g' D'
    cocone-span-extension-mathers-second-cube-theorem =
      comp-cocone-hom-span _ _ f' g'
        ( map-inv-equiv-total-fiber' hB)
        ( map-inv-equiv-total-fiber' hC)
        ( map-inv-equiv-total-fiber' hA)
        ( cocone-postcompose-mathers-second-cube-theorem)
        ( inv-htpy (back-left-mathers-cube pb-left pb-back))
        ( back-right-mathers-cube pb-left pb-back)

    universal-property-pushout-cocone-span-extension-mathers-second-cube-theorem :
      (po-bottom : universal-property-pushout f g (h , k , bottom)) →
      universal-property-pushout f' g'
        ( cocone-span-extension-mathers-second-cube-theorem)
    universal-property-pushout-cocone-span-extension-mathers-second-cube-theorem
      po-bottom =
      universal-property-pushout-extended-by-equivalences _ _ f' g'
        ( map-inv-equiv-total-fiber' hB)
        ( map-inv-equiv-total-fiber' hC)
        ( map-inv-equiv-total-fiber' hA)
        ( cocone-postcompose-mathers-second-cube-theorem)
        ( universal-property-pushout-cocone-postcompose-mathers-second-cube-theorem
          ( po-bottom))
        ( inv-htpy (back-left-mathers-cube pb-left pb-back))
        ( back-right-mathers-cube pb-left pb-back)
        ( is-equiv-map-inv-equiv-total-fiber' hB)
        ( is-equiv-map-inv-equiv-total-fiber' hC)
        ( is-equiv-map-inv-equiv-total-fiber' hA)
```

We now transfer the universal property back to a cocone on `f'` and `g'` via
total-fiber computations.

```agda
    left-eq-cocone-span-extension-mathers-second-cube-theorem :
      (x : A') →
      ap
        ( h' ∘ map-equiv-total-fiber' hB)
        ( inv
          ( eq-pair-Σ
            ( left x)
            ( inv (compute-tr-self-fiber' hB (f' x , left x))))) ＝
      refl
    left-eq-cocone-span-extension-mathers-second-cube-theorem x =
      ( ap-inv
        ( h' ∘ map-equiv-total-fiber' hB)
        ( eq-pair-Σ
          ( left x)
          ( inv (compute-tr-self-fiber' hB (f' x , left x))))) ∙
      ( ap
        ( inv)
        ( ( ap-comp h' (map-equiv-total-fiber' hB)
            ( eq-pair-Σ
              ( left x)
              ( inv (compute-tr-self-fiber' hB (f' x , left x))))) ∙
          ( ap
            ( ap h')
            ( compute-ap-map-equiv-total-fiber'-eq-pair-Σ-inv-compute-tr-self-fiber'
              hB
              ( f' x , left x)))))

    ap-map-equiv-total-fiber'-eq-pair-Σ-fiber'-mathers-second-cube-theorem :
      {y y' : D}
      (p : y ＝ y')
      {u : fiber' hD y}
      {u' : fiber' hD y'}
      (q : tr (fiber' hD) p u ＝ u') →
      ( ap (map-equiv-total-fiber' hD) (eq-pair-Σ p q)) ＝
      ( ap (inclusion-fiber' hD) (compute-tr-fiber' hD p u)) ∙
      ( ap (inclusion-fiber' hD) q)
    ap-map-equiv-total-fiber'-eq-pair-Σ-fiber'-mathers-second-cube-theorem
      refl refl =
      refl

    compute-ap-inclusion-fiber'-eq-Eq-fiber'-mathers-second-cube-theorem :
      {y : D} {s t : fiber' hD y}
      (α : inclusion-fiber' hD s ＝ inclusion-fiber' hD t)
      ( β :
        compute-value-inclusion-fiber' hD t ＝
        compute-value-inclusion-fiber' hD s ∙ ap hD α) →
      ap (inclusion-fiber' hD) (eq-Eq-fiber' hD y α β) ＝ α
    compute-ap-inclusion-fiber'-eq-Eq-fiber'-mathers-second-cube-theorem
      refl refl =
      ap-pr1-eq-pair-eq-fiber (inv right-unit)

    point-spanning-type-map-equiv-mathers-second-cube-theorem :
      (x : A') → fiber' hD (h (f (hA x)))
    point-spanning-type-map-equiv-mathers-second-cube-theorem x =
      ( ( fiberwise-map-front-mathers-cube pb-front (f (hA x))) ∘
        ( fiberwise-map-left-mathers-cube pb-left (hA x)))
        ( x , refl)

    ap-inclusion-fiber'-compute-tr-point-mathers-second-cube-theorem :
      (x : A') →
      h' (f' x) ＝
      inclusion-fiber'
        ( hD)
        ( tr
          ( fiber' hD)
          ( bottom (hA x))
          ( point-spanning-type-map-equiv-mathers-second-cube-theorem x))
    ap-inclusion-fiber'-compute-tr-point-mathers-second-cube-theorem x =
      ap
        ( inclusion-fiber' hD)
        ( compute-tr-fiber'
          ( hD)
          ( bottom (hA x))
          ( point-spanning-type-map-equiv-mathers-second-cube-theorem x))

    cancellation-inv-concat-mathers-second-cube-theorem :
      {x y z : D'} (p : x ＝ y) (q : x ＝ z) →
      p ∙ inv (inv q ∙ p) ＝ q
    cancellation-inv-concat-mathers-second-cube-theorem p q =
      ( ap (p ∙_) (distributive-inv-concat (inv q) p)) ∙
      ( is-section-inv-concat p (inv (inv q))) ∙
      ( inv-inv q)
```

The next lemmas compute how fiber inclusions and transport interact on the
middle equality.

```agda
    ap-inclusion-fiber'-middle-coherence-equiv-equifibered-span-diagram-mathers-second-cube-theorem' :
      (x : A') →
      ( ap
        ( inclusion-fiber' hD)
        ( coherence-right-equiv-equifibered-span-diagram-mathers-second-cube-theorem
          ( hA x)
          ( x , refl))) ＝
      ( inv (top x)) ∙
      ( ap-inclusion-fiber'-compute-tr-point-mathers-second-cube-theorem x)
    ap-inclusion-fiber'-middle-coherence-equiv-equifibered-span-diagram-mathers-second-cube-theorem'
      x =
      ( ap-concat
        ( inclusion-fiber' hD)
        ( eq-Eq-fiber'
          ( hD)
          ( k (g (hA x)))
          ( inv (top x))
          ( ( double-transpose-eq-concat
              ( bottom (hA x))
              ( ap h (left x) ∙ front (f' x))
              ( ap k (back x) ∙ right (g' x))
              ( ap hD (top x))
              ( c x)) ∙
            ( ap
              ( (ap k (back x) ∙ right (g' x)) ∙_)
              ( inv-ap-inv hD (top x)))))
        ( compute-tr-fiber'
          ( hD)
          ( bottom (hA x))
          ( point-spanning-type-map-equiv-mathers-second-cube-theorem x))) ∙
      ( ap
        ( _∙ ap-inclusion-fiber'-compute-tr-point-mathers-second-cube-theorem x)
        ( compute-ap-inclusion-fiber'-eq-Eq-fiber'-mathers-second-cube-theorem
          ( inv (top x))
          ( ( double-transpose-eq-concat
              ( bottom (hA x))
              ( ap h (left x) ∙ front (f' x))
              ( ap k (back x) ∙ right (g' x))
              ( ap hD (top x))
              ( c x)) ∙
            ( ap
              ( (ap k (back x) ∙ right (g' x)) ∙_)
              ( inv-ap-inv hD (top x))))))

    ap-inclusion-fiber'-middle-coherence-equiv-equifibered-span-diagram-mathers-second-cube-theorem :
      (x : A') →
      ( ap-inclusion-fiber'-compute-tr-point-mathers-second-cube-theorem x ∙
        ap
          ( inclusion-fiber' hD)
          ( inv
            ( coherence-right-equiv-equifibered-span-diagram-mathers-second-cube-theorem
              ( hA x)
              ( x , refl)))) ＝
      ( top x)
    ap-inclusion-fiber'-middle-coherence-equiv-equifibered-span-diagram-mathers-second-cube-theorem
      x =
      ( ap
        ( ap-inclusion-fiber'-compute-tr-point-mathers-second-cube-theorem x ∙_)
        ( ap-inv
          ( inclusion-fiber' hD)
          ( coherence-right-equiv-equifibered-span-diagram-mathers-second-cube-theorem
            ( hA x)
            ( x , refl)))) ∙
      ( ap
        ( λ t →
          ap-inclusion-fiber'-compute-tr-point-mathers-second-cube-theorem x ∙
          inv t)
        ( ap-inclusion-fiber'-middle-coherence-equiv-equifibered-span-diagram-mathers-second-cube-theorem'
          ( x))) ∙
      ( cancellation-inv-concat-mathers-second-cube-theorem
        ( ap-inclusion-fiber'-compute-tr-point-mathers-second-cube-theorem x)
        ( top x))

    middle-eq-cocone-span-extension-mathers-second-cube-theorem :
      (x : A') →
      ap
        ( map-equiv-total-fiber' hD)
        ( eq-pair-Σ
          ( bottom (hA x))
          ( inv
            ( coherence-right-equiv-equifibered-span-diagram-mathers-second-cube-theorem
              ( hA x)
              ( x , refl)))) ＝
      top x
    middle-eq-cocone-span-extension-mathers-second-cube-theorem x =
      ( ap-map-equiv-total-fiber'-eq-pair-Σ-fiber'-mathers-second-cube-theorem
        ( bottom (hA x))
        ( inv
          ( coherence-right-equiv-equifibered-span-diagram-mathers-second-cube-theorem
            ( hA x)
            ( x , refl)))) ∙
      ( ap-inclusion-fiber'-middle-coherence-equiv-equifibered-span-diagram-mathers-second-cube-theorem
        ( x))

    right-eq-cocone-span-extension-mathers-second-cube-theorem :
      (x : A') →
      ap
        ( k' ∘ map-equiv-total-fiber' hC)
        ( eq-pair-Σ
          ( back x)
          ( inv (compute-tr-self-fiber' hC (g' x , back x)))) ＝
      refl
    right-eq-cocone-span-extension-mathers-second-cube-theorem x =
      ( ap-comp k' (map-equiv-total-fiber' hC)
        ( eq-pair-Σ
          ( back x)
          ( inv (compute-tr-self-fiber' hC (g' x , back x))))) ∙
      ( ap
        ( ap k')
        ( compute-ap-map-equiv-total-fiber'-eq-pair-Σ-inv-compute-tr-self-fiber'
          ( hC)
          ( g' x , back x)))

    coherence-eq-cocone-span-extension-mathers-second-cube-theorem :
      statement-coherence-htpy-cocone f' g'
        ( cocone-span-extension-mathers-second-cube-theorem)
        ( h' , k' , top)
        ( refl-htpy)
        ( refl-htpy)
    coherence-eq-cocone-span-extension-mathers-second-cube-theorem x =
      ( right-unit) ∙
      ( ap-ternary
        ( λ t m r → ((t ∙ m) ∙ r))
        ( left-eq-cocone-span-extension-mathers-second-cube-theorem x)
        ( middle-eq-cocone-span-extension-mathers-second-cube-theorem x)
        ( right-eq-cocone-span-extension-mathers-second-cube-theorem x)) ∙
      ( right-unit)

    eq-cocone-span-extension-mathers-second-cube-theorem :
      cocone-span-extension-mathers-second-cube-theorem ＝
      ( h' , k' , top)
    eq-cocone-span-extension-mathers-second-cube-theorem =
      eq-htpy-cocone f' g'
        ( cocone-span-extension-mathers-second-cube-theorem)
        ( h' , k' , top)
        ( refl-htpy ,
          refl-htpy ,
          coherence-eq-cocone-span-extension-mathers-second-cube-theorem)
```

Finally, we identify the constructed cocone with the original.

```agda
    mathers-second-cube-theorem :
      universal-property-pushout f g (h , k , bottom) →
      universal-property-pushout f' g' (h' , k' , top)
    mathers-second-cube-theorem po-bottom =
      up-pushout-up-pushout-is-equiv f' g'
        ( cocone-span-extension-mathers-second-cube-theorem)
        ( h' , k' , top)
        ( id)
        ( htpy-eq-cocone f' g'
          ( cocone-map f' g'
            ( cocone-span-extension-mathers-second-cube-theorem)
            ( id))
          ( h' , k' , top)
          ( ( cocone-map-id f' g'
              ( cocone-span-extension-mathers-second-cube-theorem)) ∙
            ( eq-cocone-span-extension-mathers-second-cube-theorem)))
        ( is-equiv-id)
        ( universal-property-pushout-cocone-span-extension-mathers-second-cube-theorem
          ( po-bottom))
```

## See also

- Mather's second cube theorem is the
  [unstraightened](foundation.type-duality.md) version of the
  [flattening lemma for pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md)
- The
  [descent property for pushouts](synthetic-homotopy-theory.descent-pushouts.md).

## External links

- [Mather's Second Cube Theorem](https://kerodon.net/tag/011H) on Kerodon
