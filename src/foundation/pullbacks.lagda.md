# Pullbacks

```agda
module foundation.pullbacks where

open import foundation-core.pullbacks public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.dependent-sums-pullbacks
open import foundation.descent-equivalences
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-function-types
open import foundation.standard-pullbacks
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.diagonal-maps-cartesian-products-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.postcomposition-functions
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

Consider a [cone](foundation.cones-over-cospan-diagrams.md) over a
[cospan diagram of types](foundation.cospan-diagrams.md) `f : A -> X <- B : g,`

```text
  C ------> B
  |         |
  |         | g
  ∨         ∨
  A ------> X.
       f
```

we want to pose the question of whether this cone is a
{{#concept "pullback cone" Disambiguation="types" Agda=is-pullback}}. Although
this concept is captured by
[the universal property of the pullback](foundation-core.universal-property-pullbacks.md),
this is a large proposition, which is not suitable for all purposes. Therefore,
as our main definition of a pullback cone we consider the
{{#concept "small predicate of being a pullback" Agda=is-pullback}}: given the
existence of the [standard pullback type](foundation.standard-pullbacks.md)
`A ×_X B`, a cone is a _pullback_ if the gap map into the standard pullback is
an [equivalence](foundation-core.equivalences.md).

## Properties

### Being a pullback is a property

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  is-prop-is-pullback : (c : cone f g C) → is-prop (is-pullback f g c)
  is-prop-is-pullback c = is-property-is-equiv (gap f g c)

  is-pullback-Prop : (c : cone f g C) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 (is-pullback-Prop c) = is-pullback f g c
  pr2 (is-pullback-Prop c) = is-prop-is-pullback c
```

### The identity type as a pullback

```agda
module _
  {l : Level} {A : UU l} (x y : A)
  where

  cone-Id : cone (point x) (point y) (x ＝ y)
  cone-Id = terminal-map (x ＝ y) , terminal-map (x ＝ y) , id

  is-pullback-Id : is-pullback (point x) (point y) cone-Id
  is-pullback-Id =
    is-equiv-is-invertible
      coherence-square-standard-pullback
      refl-htpy
      refl-htpy
```

### The type of equivalences as a pullback

The type of equivalences `A ≃ B` can be presented as the following pullback.

```text
             A ≃ B ----------------------> unit
               | ⌟                          |
               |                            |
               |                            | * ↦ (id , id)
               |                            |
               |                            |
               ∨                            ∨
  (A → B) × (B → A) × (B → A) ----> (A → A) × (B → B)
                    (f , g , h) ↦ (h ∘ f , f ∘ g)
```

This presentation can be found as Proposition 2.18 in {{#cite CORS20}} and
Corollary 5.1.23 in {{#cite Rij19}}.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cone-equiv :
    cone
      ( λ (f , g , h) → h ∘ f , f ∘ g)
      ( point (id' A , id' B))
      ( A ≃ B)
  cone-equiv =
      ( λ e →
        map-equiv e , map-section-map-equiv e , map-retraction-map-equiv e) ,
      ( terminal-map (A ≃ B)) ,
      ( λ e →
        eq-pair
          ( eq-htpy (is-retraction-map-retraction-map-equiv e))
          ( eq-htpy (is-section-map-section-map-equiv e)))

  abstract
    is-pullback-equiv :
      is-pullback
        ( λ (f , g , h) → h ∘ f , f ∘ g)
        ( point (id' A , id' B))
        ( cone-equiv)
    is-pullback-equiv =
      is-equiv-is-invertible
        ( λ ((f , g , h) , * , H) →
          f , (g , htpy-eq (pr2 (pair-eq H))) , (h , htpy-eq (pr1 (pair-eq H))))
        ( λ (_ , * , H) →
          eq-pair-eq-fiber
            ( eq-pair-eq-fiber
              ( ( ap-binary
                  ( eq-pair)
                  ( is-retraction-eq-htpy (ap pr1 H))
                  ( is-retraction-eq-htpy (ap pr2 H))) ∙
                ( is-section-pair-eq H))))
        ( λ e → eq-type-subtype is-equiv-Prop refl)
```

### In a commuting cube where the front faces are pullbacks, either back face is a pullback iff the other back face is

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : A → C} {h : B → D} {k : C → D}
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  {f' : A' → B'} {g' : A' → C'} {h' : B' → D'} {k' : C' → D'}
  {hA : A' → A} {hB : B' → B} {hC : C' → C} {hD : D' → D}
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  is-pullback-back-left-is-pullback-back-right-cube :
    is-pullback h hD (hB , h' , front-left) →
    is-pullback k hD (hC , k' , front-right) →
    is-pullback g hC (hA , g' , back-right) →
    is-pullback f hB (hA , f' , back-left)
  is-pullback-back-left-is-pullback-back-right-cube
    is-pb-front-left is-pb-front-right is-pb-back-right =
    is-pullback-left-square-is-pullback-rectangle f h hD
      ( hB , h' , front-left)
      ( hA , f' , back-left)
      ( is-pb-front-left)
      ( is-pullback-htpy
        ( bottom)
        ( refl-htpy)
        ( triple
          ( hA)
          ( k' ∘ g')
          ( rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))
        ( triple
          ( refl-htpy)
          ( top)
          ( coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c))
        ( is-pullback-rectangle-is-pullback-left-square g k hD
          ( hC , k' , front-right)
          ( hA , g' , back-right)
          ( is-pb-front-right)
          ( is-pb-back-right)))

  is-pullback-back-right-is-pullback-back-left-cube :
    is-pullback h hD (hB , h' , front-left) →
    is-pullback k hD (hC , k' , front-right) →
    is-pullback f hB (hA , f' , back-left) →
    is-pullback g hC (hA , g' , back-right)
  is-pullback-back-right-is-pullback-back-left-cube
    is-pb-front-left is-pb-front-right is-pb-back-left =
    is-pullback-left-square-is-pullback-rectangle g k hD
      ( hC , k' , front-right)
      ( hA , g' , back-right)
      ( is-pb-front-right)
      ( is-pullback-htpy'
        ( bottom)
        ( refl-htpy)
        ( triple
          ( hA)
          ( h' ∘ f')
          ( rectangle-left-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))
        ( triple
          ( refl-htpy)
          ( top)
          ( coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c))
        ( is-pullback-rectangle-is-pullback-left-square f h hD
          ( hB , h' , front-left)
          ( hA , f' , back-left)
          ( is-pb-front-left)
          ( is-pb-back-left)))
```

### In a commuting cube where the vertical maps are equivalences, the bottom square is a pullback if and only if the top square is a pullback

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  is-pullback-bottom-is-pullback-top-cube-is-equiv :
    is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
    is-pullback h' k' (f' , g' , top) →
    is-pullback h k (f , g , bottom)
  is-pullback-bottom-is-pullback-top-cube-is-equiv
    is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-top =
    descent-is-equiv hB h k
      ( f , g , bottom)
      ( f' , hA , inv-htpy (back-left))
      ( is-equiv-hB)
      ( is-equiv-hA)
      ( is-pullback-htpy
        ( front-left)
        ( refl-htpy' k)
        ( triple
          ( f')
          ( hC ∘ g')
          ( rectangle-top-front-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))
        ( triple
          ( refl-htpy' f')
          ( back-right)
          ( coherence-htpy-parallel-cone-coherence-cube-maps
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c))
        ( is-pullback-rectangle-is-pullback-left-square
          ( h')
          ( hD)
          ( k)
          ( k' , hC , inv-htpy front-right)
          ( f' , g' , top)
          ( is-pullback-is-equiv-horizontal-maps hD k
            ( k' , hC , inv-htpy front-right)
            ( is-equiv-hD)
            ( is-equiv-hC))
          ( is-pb-top)))

  is-pullback-top-is-pullback-bottom-cube-is-equiv :
    is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
    is-pullback h k (f , g , bottom) →
    is-pullback h' k' (f' , g' , top)
  is-pullback-top-is-pullback-bottom-cube-is-equiv
    is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-bottom =
    is-pullback-top-square-is-pullback-rectangle h hD k'
      ( hB , h' , front-left)
      ( f' , g' , top)
      ( is-pullback-is-equiv-vertical-maps h hD
        ( hB , h' , front-left)
        is-equiv-hD is-equiv-hB)
      ( is-pullback-htpy' refl-htpy front-right
        ( pasting-vertical-cone h k hC
          ( f , g , bottom)
          ( hA , g' , back-right))
        ( triple
          ( back-left)
          ( refl-htpy)
          ( ( assoc-htpy
              ( bottom ·r hA)
              ( k ·l back-right)
              ( front-right ·r g')) ∙h
            ( inv-htpy c) ∙h
            ( assoc-htpy (h ·l back-left) (front-left ·r f') (hD ·l top)) ∙h
            ( ap-concat-htpy'
              ( (front-left ·r f') ∙h (hD ·l top))
              ( inv-htpy-right-unit-htpy {H = h ·l back-left}))))
        ( is-pullback-rectangle-is-pullback-top-square h k hC
          ( f , g , bottom)
          ( hA , g' , back-right)
          ( is-pb-bottom)
          ( is-pullback-is-equiv-vertical-maps g hC
            ( hA , g' , back-right)
            is-equiv-hC is-equiv-hA)))
```

### In a commuting cube where the maps from back-right to front-left are equivalences, the back-right square is a pullback if and only if the front-left square is a pullback

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  is-pullback-front-left-is-pullback-back-right-cube-is-equiv :
    is-equiv f' → is-equiv f → is-equiv k' → is-equiv k →
    is-pullback g hC (hA , g' , back-right) →
    is-pullback h hD (hB , h' , front-left)
  is-pullback-front-left-is-pullback-back-right-cube-is-equiv
    is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right =
    is-pullback-bottom-is-pullback-top-cube-is-equiv
      hB h' h hD hA g' g hC f' f k' k
      back-right (inv-htpy back-left) top bottom (inv-htpy front-right)
      ( front-left)
      ( coherence-cube-maps-mirror-B f g h k f' g' h' k' hA hB hC hD top
        back-left back-right front-left front-right bottom c)
      is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right

  is-pullback-front-right-is-pullback-back-left-cube-is-equiv :
    is-equiv g' → is-equiv h' → is-equiv g → is-equiv h →
    is-pullback f hB (hA , f' , back-left) →
    is-pullback k hD (hC , k' , front-right)
  is-pullback-front-right-is-pullback-back-left-cube-is-equiv
    is-equiv-g' is-equiv-h' is-equiv-g is-equiv-h is-pb-back-left =
    is-pullback-bottom-is-pullback-top-cube-is-equiv
      hC k' k hD hA f' f hB g' g h' h
      back-left (inv-htpy back-right) (inv-htpy top)
      ( inv-htpy bottom) (inv-htpy front-left) front-right
      ( coherence-cube-maps-rotate-120 f g h k f' g' h' k' hA hB hC hD
        top back-left back-right front-left front-right bottom c)
      is-equiv-g' is-equiv-g is-equiv-h' is-equiv-h is-pb-back-left
```

### Identity types commute with pullbacks

Given a pullback square

```text
         f'
    C -------> B
    | ⌟        |
  g'|          | g
    ∨          ∨
    A -------> X
         f
```

and two elements `u` and `v` of `C`, then the induced square

```text
                ap f'
     (u ＝ v) --------> (f' u ＝ f' v)
        |                     |
  ap g' |                     |
        ∨                     ∨
  (g' u ＝ g' v) -> (f (g' u) ＝ g (f' v))
```

is also a pullback.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  cone-ap :
    (u v : C) →
    cone
      ( λ (α : vertical-map-cone f g c u ＝ vertical-map-cone f g c v) →
        ap f α ∙ coherence-square-cone f g c v)
      ( λ (β : horizontal-map-cone f g c u ＝ horizontal-map-cone f g c v) →
        coherence-square-cone f g c u ∙ ap g β)
      ( u ＝ v)
  pr1 (cone-ap u v) = ap (vertical-map-cone f g c)
  pr1 (pr2 (cone-ap u v)) = ap (horizontal-map-cone f g c)
  pr2 (pr2 (cone-ap u v)) γ =
    ( right-whisker-concat
      ( inv (ap-comp f (vertical-map-cone f g c) γ))
      ( coherence-square-cone f g c v)) ∙
    ( ( inv-nat-htpy (coherence-square-cone f g c) γ) ∙
      ( left-whisker-concat
        ( coherence-square-cone f g c u)
        ( ap-comp g (horizontal-map-cone f g c) γ)))

  cone-ap' :
    (u v : C) →
    cone
      ( λ (α : vertical-map-cone f g c u ＝ vertical-map-cone f g c v) →
        tr
          ( f (vertical-map-cone f g c u) ＝_)
          ( coherence-square-cone f g c v)
          ( ap f α))
      ( λ (β : horizontal-map-cone f g c u ＝ horizontal-map-cone f g c v) →
        coherence-square-cone f g c u ∙ ap g β)
      ( u ＝ v)
  pr1 (cone-ap' u v) = ap (vertical-map-cone f g c)
  pr1 (pr2 (cone-ap' u v)) = ap (horizontal-map-cone f g c)
  pr2 (pr2 (cone-ap' u v)) γ =
    ( tr-Id-right
      ( coherence-square-cone f g c v)
      ( ap f (ap (vertical-map-cone f g c) γ))) ∙
    ( ( right-whisker-concat
        ( inv (ap-comp f (vertical-map-cone f g c) γ))
        ( coherence-square-cone f g c v)) ∙
      ( ( inv-nat-htpy (coherence-square-cone f g c) γ) ∙
        ( left-whisker-concat
          ( coherence-square-cone f g c u)
          ( ap-comp g (horizontal-map-cone f g c) γ))))

  abstract
    is-pullback-cone-ap :
      is-pullback f g c →
      (u v : C) →
      is-pullback
        ( λ (α : vertical-map-cone f g c u ＝ vertical-map-cone f g c v) →
          ap f α ∙ coherence-square-cone f g c v)
        ( λ (β : horizontal-map-cone f g c u ＝ horizontal-map-cone f g c v) →
          coherence-square-cone f g c u ∙ ap g β)
        ( cone-ap u v)
    is-pullback-cone-ap is-pb-c u v =
      is-pullback-htpy'
        ( λ α → tr-Id-right (coherence-square-cone f g c v) (ap f α))
        ( refl-htpy)
        ( cone-ap' u v)
        ( refl-htpy , refl-htpy , right-unit-htpy)
        ( is-pullback-family-is-pullback-tot
          ( f (vertical-map-cone f g c u) ＝_)
          ( λ a → ap f {x = vertical-map-cone f g c u} {y = a})
          ( λ b β → coherence-square-cone f g c u ∙ ap g β)
          ( c)
          ( cone-ap' u)
          ( is-pb-c)
          ( is-pullback-is-equiv-vertical-maps
            ( map-Σ _ f (λ a α → ap f α))
            ( map-Σ _ g (λ b β → coherence-square-cone f g c u ∙ ap g β))
            ( tot-cone-cone-family
              ( f (vertical-map-cone f g c u) ＝_)
              ( λ a → ap f)
              ( λ b β → coherence-square-cone f g c u ∙ ap g β)
              ( c)
              ( cone-ap' u))
            ( is-equiv-is-contr _
              ( is-torsorial-Id (horizontal-map-cone f g c u))
              ( is-torsorial-Id (f (vertical-map-cone f g c u))))
            ( is-equiv-is-contr _
              ( is-torsorial-Id u)
              ( is-torsorial-Id (vertical-map-cone f g c u))))
          ( v))
```

## References

{{#bibliography}}

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
