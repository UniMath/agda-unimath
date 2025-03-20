# Functorialty of pullbacks

```agda
open import foundation.function-extensionality-axiom

module
  foundation.functoriality-pullbacks
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams funext
open import foundation.cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types funext
open import foundation.function-types funext
open import foundation.homotopies funext
open import foundation.homotopies funext-morphisms-cospan-diagrams
open import foundation.morphisms-cospan-diagrams
open import foundation.pullback-cones funext
open import foundation.standard-pullbacks funext
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.pullbacks funext
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
  map-standard-pullback (hA , hB , hX , HA , HB) (a' , b' , p') =
    ( hA a' , hB b' , HA a' ∙ ap hX p' ∙ inv (HB b'))

  map-pullback-cone :
    {l4 l4' : Level} (c : pullback-cone 𝒮 l4) (c' : pullback-cone 𝒯 l4') →
    hom-cospan-diagram 𝒮 𝒯 →
    domain-pullback-cone 𝒮 c → domain-pullback-cone 𝒯 c'
  map-pullback-cone c c' h x =
    map-inv-is-equiv
      ( is-pullback-pullback-cone 𝒯 c')
      ( map-standard-pullback h
        ( gap
          ( left-map-cospan-diagram 𝒮)
          ( right-map-cospan-diagram 𝒮)
          ( cone-pullback-cone 𝒮 c)
          ( x)))
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

  preserves-id-map-pullback-cone :
    {l4 : Level} (c : pullback-cone 𝒮 l4) →
    map-pullback-cone 𝒮 𝒮 c c (id-hom-cospan-diagram 𝒮) ~ id
  preserves-id-map-pullback-cone c =
    ( ( map-inv-is-equiv (is-pullback-pullback-cone 𝒮 c)) ·l
      ( preserves-id-map-standard-pullback) ·r
      ( gap
        ( left-map-cospan-diagram 𝒮)
        ( right-map-cospan-diagram 𝒮)
        ( cone-pullback-cone 𝒮 c))) ∙h
    ( is-retraction-map-inv-is-equiv (is-pullback-pullback-cone 𝒮 c))
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

  preserves-comp-map-pullback-cone :
    {l4 l4' l4'' : Level}
    (c : pullback-cone 𝒮 l4)
    (c' : pullback-cone 𝒯 l4')
    (c'' : pullback-cone ℛ l4'')
    (h : hom-cospan-diagram 𝒯 ℛ)
    (h' : hom-cospan-diagram 𝒮 𝒯) →
    map-pullback-cone 𝒮 ℛ c c'' (comp-hom-cospan-diagram 𝒮 𝒯 ℛ h h') ~
    map-pullback-cone 𝒯 ℛ c' c'' h ∘
    map-pullback-cone 𝒮 𝒯 c c' h'
  preserves-comp-map-pullback-cone c c' c'' h h' =
    ( ( map-inv-is-equiv (is-pullback-pullback-cone ℛ c'')) ·l
      ( ( preserves-comp-map-standard-pullback h h') ∙h
        ( ( map-standard-pullback 𝒯 ℛ h) ·l
          ( inv-htpy
            ( is-section-map-inv-is-equiv (is-pullback-pullback-cone 𝒯 c'))) ·r
          ( map-standard-pullback 𝒮 𝒯 h'))) ·r
      ( gap
        ( left-map-cospan-diagram 𝒮)
        ( right-map-cospan-diagram 𝒮)
        ( cone-pullback-cone 𝒮 c)))
```

### The functorial action on maps of pullbacks preserves homotopies

We show that the functorial action on maps of pullbacks preserves homotopies
without appealing to the function extensionality axiom.

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  where

  coherence-preserves-htpy-map-standard-pullback :
    (𝒮 : cospan-diagram l1 l2 l3)
    (𝒯 : cospan-diagram l1' l2' l3')
    (h h' : hom-cospan-diagram 𝒮 𝒯)
    (H : htpy-hom-cospan-diagram 𝒮 𝒯 h h') →
    (t :
      standard-pullback
        ( left-map-cospan-diagram 𝒮)
        ( right-map-cospan-diagram 𝒮)) →
    coherence-Eq-standard-pullback
      ( left-map-cospan-diagram 𝒯)
      ( right-map-cospan-diagram 𝒯)
      ( map-standard-pullback 𝒮 𝒯 h t)
      ( map-standard-pullback 𝒮 𝒯 h' t)
      ( htpy-left-map-htpy-hom-cospan-diagram 𝒮 𝒯 h h' H
        ( vertical-map-standard-pullback t))
      ( htpy-right-map-htpy-hom-cospan-diagram 𝒮 𝒯 h h' H
        ( horizontal-map-standard-pullback t))
  coherence-preserves-htpy-map-standard-pullback
    𝒮@(A , B , X , f , g)
    𝒯@(A' , B' , X' , f' , g')
    h@(hA , hB , hX , HA , HB)
    h'@(hA' , hB' , hX' , HA' , HB')
    (HHA , HHB , HHX , K , L)
    (x , y , p) =
    equational-reasoning
    ap f' (HHA x) ∙ ((HA' x ∙ ap hX' p) ∙ inv (HB' y))
    ＝ (HA x ∙ (ap hX p ∙ HHX (g y))) ∙ inv (HB' y)
    by
      ( inv (assoc (ap f' (HHA x)) (HA' x ∙ ap hX' p) (inv (HB' y)))) ∙
      ( ap
        ( _∙ inv (HB' y))
        ( ( inv (assoc (ap f' (HHA x)) (HA' x) (ap hX' p))) ∙
          ( ap (_∙ ap hX' p) (inv (K x))) ∙
          ( assoc (HA x) (HHX (f x)) (ap hX' p)) ∙
          ( ap (HA x ∙_) (nat-htpy HHX p))))
    ＝ HA x ∙ (ap hX p ∙ (inv (HB y) ∙ ap g' (HHB y)))
    by
      ( assoc (HA x) (ap hX p ∙ HHX (g y)) (inv (HB' y))) ∙
      ( ap
        ( HA x ∙_)
        ( ( assoc (ap hX p) (HHX (g y)) (inv (HB' y))) ∙
          ( ap
            ( ap hX p ∙_)
            ( double-transpose-eq-concat'
              ( ap g' (HHB y))
              ( HB y)
              ( HB' y)
              ( HHX (g y))
              ( L y)))))
    ＝ ((HA x ∙ ap hX p) ∙ inv (HB y)) ∙ ap g' (HHB y)
    by
      ( inv (assoc (HA x) (ap hX p) (inv (HB y) ∙ ap g' (HHB y)))) ∙
      ( inv (assoc (HA x ∙ ap hX p) (inv (HB y)) (ap g' (HHB y))))

  preserves-htpy-map-standard-pullback :
    (𝒮 : cospan-diagram l1 l2 l3)
    (𝒯 : cospan-diagram l1' l2' l3')
    (h h' : hom-cospan-diagram 𝒮 𝒯)
    (H : htpy-hom-cospan-diagram 𝒮 𝒯 h h') →
    map-standard-pullback 𝒮 𝒯 h ~ map-standard-pullback 𝒮 𝒯 h'
  preserves-htpy-map-standard-pullback 𝒮 𝒯 h h' H t =
    eq-Eq-standard-pullback
      ( left-map-cospan-diagram 𝒯)
      ( right-map-cospan-diagram 𝒯)
      ( htpy-left-map-htpy-hom-cospan-diagram 𝒮 𝒯 h h' H
        ( vertical-map-standard-pullback t))
      ( htpy-right-map-htpy-hom-cospan-diagram 𝒮 𝒯 h h' H
        ( horizontal-map-standard-pullback t))
      ( coherence-preserves-htpy-map-standard-pullback 𝒮 𝒯 h h' H t)

module _
  {l1 l2 l3 l1' l2' l3' : Level}
  (𝒮 : cospan-diagram l1 l2 l3)
  (𝒯 : cospan-diagram l1' l2' l3')
  {l4 l4' : Level}
  (c : pullback-cone 𝒮 l4)
  (c' : pullback-cone 𝒯 l4')
  (h h' : hom-cospan-diagram 𝒮 𝒯)
  (H : htpy-hom-cospan-diagram 𝒮 𝒯 h h')
  where

  preserves-htpy-map-pullback-cone :
    map-pullback-cone 𝒮 𝒯 c c' h ~
    map-pullback-cone 𝒮 𝒯 c c' h'
  preserves-htpy-map-pullback-cone =
    ( map-inv-is-equiv (is-pullback-pullback-cone 𝒯 c')) ·l
    ( preserves-htpy-map-standard-pullback 𝒮 𝒯 h h' H) ·r
    ( gap
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( cone-pullback-cone 𝒮 c))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
