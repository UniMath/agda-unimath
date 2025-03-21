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
that every base change of a pushout square is a pushout. In other words, if we
are given a commuting cube where the bottom face is a pushout and the vertical
faces are pullbacks

```text
  ∙ ----------------> ∙
  | \ ⌟               | \
  | ⌟\                | ⌟\
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
        equational-reasoning
        g (hA x) , {! pr1 (pr1 (pr1 (is-fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback' k hD (hC , k' , right) pb-right (g (pr1 (map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA) x))))) (pr1 (equiv-tr (fiber' hD) (bottom (pr1 (map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA) x))) ∘e e-front (f (pr1 (map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA) x)))) (pr2 (map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA) x)))) !} , {! pr2 (pr1 (pr1 (is-fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback' k hD (hC , k' , right) pb-right (g (pr1 (map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA) x))))) (pr1 (equiv-tr (fiber' hD) (bottom (pr1 (map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA) x))) ∘e e-front (f (pr1 (map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA) x)))) (pr2 (map-equiv (equiv-tot e-left ∘e inv-equiv-total-fiber' hA) x)))) !}
        ＝ hC (g' x) , g' x , refl
        by
          eq-pair-Σ
            ( back x)
            ( equational-reasoning {!   !} ＝ g' x , refl by {!   !}))
      ( λ x →
        eq-pair-Σ (front x) (inv-compute-tr-self-fiber' hD (h' x , front x)))
      ( λ x →
        eq-pair-Σ (right x) (inv-compute-tr-self-fiber' hD (k' x , right x)))
      ( λ x → {!   !})
        -- equational-reasoning
        -- {! pr1
        --   (map-Σ
        --    (λ x₁ →
        --       Id
        --       (h
        --        (pr1
        --         (vertical-map-span-flattening-descent-data-pushout
        --          (fiber' hB ,
        --           fiber' hC ,
        --           (λ s →
        --              inv-equiv (e-right (g s)) ∘e
        --              equiv-tr (fiber' hD) (bottom s) ∘e e-front (f s)))
        --          x)))
        --       (hD x₁))
        --    h' (λ a p → ap h p ∙ front a)
        --    (pr2
        --     (vertical-map-span-flattening-descent-data-pushout
        --      (fiber' hB ,
        --       fiber' hC ,
        --       (λ s →
        --          inv-equiv (e-right (g s)) ∘e
        --          equiv-tr (fiber' hD) (bottom s) ∘e e-front (f s)))
        --      x))) !} ,  , {!   !}
        -- ＝ {!   !} , {!   !} , {!   !} by {!   !})
      {!   !}
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
    -- universal-property-pushout-top-universal-property-pushout-bottom-cube-equiv
    --   ( vertical-map-span-flattening-pushout (fiber' hD) f g (h , k , bottom))
    --   ( horizontal-map-span-flattening-pushout (fiber' hD) f g (h , k , bottom))
    --   ( horizontal-map-cocone-flattening-pushout (fiber' hD) f g (h , k , bottom))
    --   ( vertical-map-cocone-flattening-pushout (fiber' hD) f g (h , k , bottom))
    --   f' g' h' k'
    --   ( equiv-tot
    --     ( λ x →
    --       ( fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
    --         h hD (hB , h' , front) pb-front (f x)) ∘e
    --       ( fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
    --         f hB (hA , f' , left) pb-left x)) ∘e
    --     ( inv-equiv-total-fiber' hA))
    --   ( ( equiv-tot-map-fiber-vertical-map-cone-universal-property-pullback'
    --       h hD
    --       ( hB , h' , front)
    --       ( pb-front)) ∘e
    --     ( inv-equiv-total-fiber' hB))
    --   ( ( equiv-tot-map-fiber-vertical-map-cone-universal-property-pullback'
    --       k hD
    --       ( hC , k' , right)
    --       ( pb-right)) ∘e
    --     ( inv-equiv-total-fiber' hC))
    --   ( inv-equiv-total-fiber' hD)
    --   ( top)
    --   ( λ x →
    --     equational-reasoning
    --       ( f (hA x) , h' (f' x) , ap h (left x) ∙ front (f' x))
    --       ＝ ( hB (f' x) , h' (f' x) , {!   !}) by {!   !}
    --       ＝ ( hB (f' x) , h' (f' x) , front (f' x)) by {!   !})
    --   (λ x → equational-reasoning g (hA x) , {!pr1 (tr (λ b → Σ D' (λ x₁ → Id b (hD x₁))) (bottom (hA x)) (map-Σ (λ x₁ → Id (h (f (hA x))) (hD x₁)) h' (λ a p → ap h p ∙ front a) (map-Σ (λ x₁ → Id (f (hA x)) (hB x₁)) f' (λ a p → ap f p ∙ left a) (pr2 (map-inv-equiv-total-fiber' hA x))))) !} , {!   !} ＝ hC (g' x) , {! pr1 (map-Σ  (λ x₁ →     map-codomain-hom-arrow hC hD     (hom-arrow-cone k hD (hC , k' , right))     (pr1 (pr1 (inv-equiv-total-fiber' hC) (g' x)))     ＝ hD x₁)  (pr1 (hom-arrow-cone k hD (hC , k' , right)))  (λ a p →     ap     (map-codomain-hom-arrow hC hD      (hom-arrow-cone k hD (hC , k' , right)))     p     ∙ coh-hom-arrow hC hD (hom-arrow-cone k hD (hC , k' , right)) a)  (pr2 (pr1 (inv-equiv-total-fiber' hC) (g' x)))) !} , {!   !} by {!   !})
    --   {!   !}
    --   {!   !}
    --   ( λ x → eq-pair-Σ (bottom (pr1 x)) refl)
    --   {!   !}
    --   ( flattening-lemma-pushout (fiber' hD) f g (h , k , bottom) po-bottom)

    -- universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv
    --   f' g' h' k'
    --   ( vertical-map-span-flattening-pushout (fiber hD) f g (h , k , bottom))
    --   ( horizontal-map-span-flattening-pushout (fiber hD) f g (h , k , bottom))
    --   ( horizontal-map-cocone-flattening-pushout (fiber hD) f g (h , k , bottom))
    --   ( vertical-map-cocone-flattening-pushout (fiber hD) f g (h , k , bottom))
    --   (map-equiv-total-fiber hA ∘ tot (λ x → {!   !} ))
    --   {!   !}
    --   {!   !}
    --   ( map-equiv-total-fiber hD)
    --   ( λ x → eq-pair-Σ (bottom (pr1 x)) refl)
    --   {!   !}
    --   {!   !}
    --   {!   !}
    --   {!   !}
    --   top
    --   {!   !}
    --   {!   !}
    --   {!   !}
    --   {!   !}
    --   ( is-equiv-map-equiv-total-fiber hD)
    --   ( flattening-lemma-pushout (fiber hD) f g (h , k , bottom) po-bottom)
```

## See also

- Mather's second cube theorem is an
  [unstraightened](foundation.type-duality.md) rephrasing of the
  [flattening lemma for pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md)
- The
  [descent property for pushouts](synthetic-homotopy-theory.descent-property-pushouts.md).

## External links

- [Mather's Second Cube Theorem](https://kerodon.net/tag/011H) on Kerodon
