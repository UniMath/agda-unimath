# Functorialty of pullbacks

```agda
module foundation.functoriality-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.morphisms-cospan-diagrams
open import foundation.standard-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.pullbacks
```

</details>

## Idea

The construction of the [standard pullback](foundation-core.pullbacks.md) is
functorial.

## Definitions

### The functorial action on maps of pullbacks

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  (𝒮 : cospan-diagram l1 l2 l3)
  (𝒯 : cospan-diagram l1' l2' l3')
  where

  map-standard-pullback :
    hom-cospan-diagram 𝒮 𝒯 →
    standard-pullback (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) →
    standard-pullback (left-map-cospan-diagram 𝒯) (right-map-cospan-diagram 𝒯)
  pr1 (map-standard-pullback (hA , _) (a' , _)) = hA a'
  pr1 (pr2 (map-standard-pullback (hA , hB , _) (a' , b' , _))) = hB b'
  pr2 (pr2 (map-standard-pullback (hA , hB , hX , HA , HB) (a' , b' , p'))) =
    HA a' ∙ ap hX p' ∙ inv (HB b')

  map-is-pullback :
    {l4 l4' : Level} {C : UU l4} {C' : UU l4'} →
    (c : cone (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) C)
    (c' : cone (left-map-cospan-diagram 𝒯) (right-map-cospan-diagram 𝒯) C') →
    is-pullback (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) c →
    is-pullback (left-map-cospan-diagram 𝒯) (right-map-cospan-diagram 𝒯) c' →
    hom-cospan-diagram 𝒮 𝒯 → C → C'
  map-is-pullback c c' is-pb-c is-pb-c' h x =
    map-inv-is-equiv is-pb-c' (map-standard-pullback h (gap (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) c x))
```

## Properties

### The functorial action on maps of pullbacks preserves identities

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : cospan-diagram l1 l2 l3)
  where

  preserves-id-map-standard-pullback :
    map-standard-pullback 𝒮 𝒮 (id-hom-cospan-diagram 𝒮) ~ id
  preserves-id-map-standard-pullback x =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( right-unit ∙ ap-id (coherence-square-standard-pullback x)))

  preserves-id-map-is-pullback :
    {l4 : Level} {C : UU l4}
    (c :
      cone (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) C)
    (pb-c :
      is-pullback (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) c) →
    map-is-pullback 𝒮 𝒮 c c pb-c pb-c (id-hom-cospan-diagram 𝒮) ~ id
  preserves-id-map-is-pullback c pb-c =
    ( ( map-inv-is-equiv pb-c) ·l
      ( preserves-id-map-standard-pullback) ·r
      ( gap (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) c)) ∙h
   ( is-retraction-map-inv-is-equiv pb-c)
```

### The functorial action on maps of pullbacks preserves composition

```agda
module _
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  (𝒮 : cospan-diagram l1 l2 l3)
  (𝒯 : cospan-diagram l1' l2' l3')
  (ℛ : cospan-diagram l1'' l2'' l3'')
  where

  preserves-comp-map-standard-pullback :
    (h : hom-cospan-diagram 𝒯 ℛ)
    (h' : hom-cospan-diagram 𝒮 𝒯) →
    map-standard-pullback 𝒮 ℛ (comp-hom-cospan-diagram 𝒮 𝒯 ℛ h h') ~
    map-standard-pullback 𝒯 ℛ h ∘ map-standard-pullback 𝒮 𝒯 h'
  preserves-comp-map-standard-pullback
    ( hA , hB , hX , H , K) (hA' , hB' , hX' , H' , K') (x , y , p) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( ( ap
            ( H (hA' x) ∙ ap hX (H' x) ∙ ap (hX ∘ hX') p ∙_)
            ( ( distributive-inv-concat (K (hB' y)) (ap hX (K' y))) ∙
              ( ap (_∙ inv (K (hB' y))) (inv (ap-inv hX (K' y)))))) ∙
          ( inv
            ( assoc
              ( H (hA' x) ∙ ap hX (H' x) ∙ ap (hX ∘ hX') p)
              ( ap hX (inv (K' y)))
              ( inv (K (hB' y))))) ∙
          ( ap
            ( _∙ (inv (K (hB' y))))
            ( ( assoc
                ( H (hA' x) ∙ ap hX (H' x))
                ( ap (hX ∘ hX') p)
                ( ap hX (inv (K' y)))) ∙
              ( ap
                ( H (hA' x) ∙ ap hX (H' x) ∙_)
                ( ( ap (_∙ ap hX (inv (K' y))) (ap-comp hX hX' p)) ∙
                  ( inv (ap-concat hX (ap hX' p) (inv (K' y))))) ∙
                ( ( assoc
                    ( H (hA' x))
                    ( ap hX (H' x))
                    ( ap hX (ap hX' p ∙ inv (K' y)))) ∙
                  ( ap
                    ( H (hA' x) ∙_)
                    ( ( inv (ap-concat hX (H' x) (ap hX' p ∙ inv (K' y)))) ∙
                      ( ap
                        ( ap hX)
                        ( inv (assoc (H' x) (ap hX' p) (inv (K' y)))))))))))))

  preserves-comp-map-is-pullback :
    {l4 l4' l4'' : Level} {C : UU l4} {C' : UU l4'} {C'' : UU l4''} →
    (c : cone (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) C)
    (c' : cone (left-map-cospan-diagram 𝒯) (right-map-cospan-diagram 𝒯) C') →
    (c'' : cone (left-map-cospan-diagram ℛ) (right-map-cospan-diagram ℛ) C'') →
    (pb-c :
      is-pullback (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) c) →
    (pb-c' :
      is-pullback (left-map-cospan-diagram 𝒯) (right-map-cospan-diagram 𝒯) c') →
    (pb-c'' :
      is-pullback
        ( left-map-cospan-diagram ℛ)
        ( right-map-cospan-diagram ℛ)
        ( c'')) →
    (h : hom-cospan-diagram 𝒯 ℛ) →
    (h' : hom-cospan-diagram 𝒮 𝒯) →
    map-is-pullback 𝒮 ℛ c c'' pb-c pb-c'' (comp-hom-cospan-diagram 𝒮 𝒯 ℛ h h') ~
    map-is-pullback 𝒯 ℛ c' c'' pb-c' pb-c'' h ∘
    map-is-pullback 𝒮 𝒯 c c' pb-c pb-c' h'
  preserves-comp-map-is-pullback c c' c'' pb-c pb-c' pb-c'' h h' =
    ( ( map-inv-is-equiv pb-c'') ·l
      ( ( preserves-comp-map-standard-pullback h h') ∙h
        ( ( map-standard-pullback 𝒯 ℛ h) ·l
          ( inv-htpy (is-section-map-inv-is-equiv pb-c')) ·r
          ( map-standard-pullback 𝒮 𝒯 h'))) ·r
      ( gap (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) c))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
