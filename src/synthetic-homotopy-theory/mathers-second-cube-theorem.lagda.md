# Mather's second cube theorem

```agda
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

```text
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
    universal-property-pushout-top-universal-property-pushout-bottom-cube-equiv
      _ _ _ _
      f' g' h' k'
      ( equiv-tot e-left ∘e inv-equiv-total-fiber' hA)
      ( inv-equiv-total-fiber' hB)
      ( inv-equiv-total-fiber' hC)
      ( inv-equiv-total-fiber' hD)
      ( top)
      ( λ x →
        eq-pair-Σ (left x) (inv-compute-tr-self-fiber' hB (f' x , left x)))
      ( λ x →
        eq-pair-Σ (back x) {!   !})
      ( λ x →
        eq-pair-Σ (front x) (inv-compute-tr-self-fiber' hD (h' x , front x)))
      ( λ x →
        eq-pair-Σ (right x) (inv-compute-tr-self-fiber' hD (k' x , right x)))
      ( {!   !})
      ( {!   !})
      ( flattening-lemma-descent-data-pushout
        ( f)
        ( g)
        ( h , k , bottom)
        ( ( fiber' hB) ,
          ( fiber' hC) ,
          ( λ s →
            ( inv-equiv (e-right (g s))) ∘e
            ( equiv-tr (fiber' hD) (bottom s)) ∘e
            ( e-front (f s))))
        ( fiber' hD)
        ( ( e-front) ,
          ( e-right) ,
          {!   !})
        ( po-bottom))
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
```

## See also

- Mather's second cube theorem is the
  [unstraightened](foundation.type-duality.md) version of the
  [flattening lemma for pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md)
- The
  [descent property for pushouts](synthetic-homotopy-theory.descent-property-pushouts.md).

## External links

- [Mather's Second Cube Theorem](https://kerodon.net/tag/011H) on Kerodon
