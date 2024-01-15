# The dependent pullback property of pushouts

```agda
module synthetic-homotopy-theory.dependent-pullback-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.pullbacks
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

The {{#concept "dependent pullback property" Disambiguation="pushouts"}} of
[pushouts](synthetic-homotopy-theory.pushouts.md) asserts that the type of
sections of a type family over a pushout can be expressed as a
[pullback](foundation.pullbacks.md).

The fact that the dependent pullback property of pushouts is
[logically equivalent](foundation.logical-equivalences.md) to the
[dependent universal property](synthetic-homotopy-theory.dependent-universal-property-pushouts.md)
of pushouts is shown in
[`dependent-universal-property-pushouts`](synthetic-homotopy-theory.dependent-universal-property-pushouts.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  cone-dependent-pullback-property-pushout :
    {l5 : Level} (P : X → UU l5) →
    cone
      ( λ ( h :
            ( a : domain-span-diagram 𝒮) →
            P (left-map-cocone-span-diagram 𝒮 c a))
          ( s : spanning-type-span-diagram 𝒮) →
        tr P
          ( coherence-square-cocone-span-diagram 𝒮 c s)
          ( h (left-map-span-diagram 𝒮 s)))
      ( λ ( h :
            ( b : codomain-span-diagram 𝒮) →
            P (right-map-cocone-span-diagram 𝒮 c b))
          ( s : spanning-type-span-diagram 𝒮) →
        h (right-map-span-diagram 𝒮 s))
      ( (x : X) → P x)
  pr1 (cone-dependent-pullback-property-pushout P) h a =
    h (left-map-cocone-span-diagram 𝒮 c a)
  pr1 (pr2 (cone-dependent-pullback-property-pushout P)) h b =
    h (right-map-cocone-span-diagram 𝒮 c b)
  pr2 (pr2 (cone-dependent-pullback-property-pushout P)) h =
    eq-htpy (λ s → apd h (coherence-square-cocone-span-diagram 𝒮 c s))

  dependent-pullback-property-pushout : UUω
  dependent-pullback-property-pushout =
    {l : Level} (P : X → UU l) →
    is-pullback
      ( λ ( h :
            ( a : domain-span-diagram 𝒮) →
            P (left-map-cocone-span-diagram 𝒮 c a))
          ( s : spanning-type-span-diagram 𝒮) →
        tr P
          ( coherence-square-cocone-span-diagram 𝒮 c s)
          ( h (left-map-span-diagram 𝒮 s)))
      ( λ ( h :
            ( b : codomain-span-diagram 𝒮) →
            P (right-map-cocone-span-diagram 𝒮 c b))
          ( s : spanning-type-span-diagram 𝒮) →
        h (right-map-span-diagram 𝒮 s))
      ( cone-dependent-pullback-property-pushout P)
```
