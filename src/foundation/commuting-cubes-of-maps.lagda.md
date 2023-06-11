# Commuting cubes of maps

```agda
module foundation.commuting-cubes-of-maps where

open import foundation-core.commuting-cubes-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Properties

### Any coherence of commuting cubes induces a coherence of parallel cones

```agda
coherence-htpy-parallel-cone-coherence-cube-maps :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c :
    coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
    top back-left back-right front-left front-right bottom) →
  coherence-htpy-parallel-cone
    ( front-left)
    ( refl-htpy' k)
    ( pair f'
      ( pair
        ( g ∘ hA)
        ( rectangle-back-left-bottom-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
    ( pair f'
      ( pair
        ( hC ∘ g')
        ( rectangle-top-front-right-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
    ( refl-htpy' f')
    ( back-right)
coherence-htpy-parallel-cone-coherence-cube-maps
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c =
  ( assoc-htpy
    ( h ·l (inv-htpy back-left))
    ( bottom ·r hA)
    ( (k ·l back-right) ∙h (refl-htpy' (k ∘ (hC ∘ g'))))) ∙h
  ( ( ap-concat-htpy'
      ( h ·l (inv-htpy back-left))
      ( inv-htpy (h ·l back-left))
      ( _)
      ( left-whisk-inv-htpy h back-left)) ∙h
    ( inv-htpy-inv-con-htpy (h ·l back-left) _ _
      ( ( (inv-htpy-assoc-htpy (h ·l back-left) (front-left ·r f') _) ∙h
          ( ( inv-htpy-assoc-htpy
              ( (h ·l back-left) ∙h (front-left ·r f'))
              ( hD ·l top)
              ( (inv-htpy front-right) ·r g')) ∙h
            ( inv-htpy-con-inv-htpy _ (front-right ·r g') _
              ( (assoc-htpy (bottom ·r hA) _ _) ∙h (inv-htpy c))))) ∙h
        ( ap-concat-htpy (bottom ·r hA) _ _ inv-htpy-right-unit-htpy))))
```
