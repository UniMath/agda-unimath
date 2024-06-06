# Morphisms of span diagrams

```agda
module foundation.morphisms-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.morphisms-spans
open import foundation.operations-spans
open import foundation.span-diagrams
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
```

</details>

## Idea

A {{#concept "morphism of span diagrams" Agda=hom-span-diagram}} from a
[span diagram](foundation.span-diagrams.md) `A <-f- S -g-> B` to a span diagram
`C <-h- T -k-> D` consists of maps `u : A → C`, `v : B → D`, and `w : S → T`
[equipped](foundation.structure.md) with two
[homotopies](foundation-core.homotopies.md) witnessing that the diagram

```text
         f       g
    A <───── S ─────> B
    │        │        │
  u │        │ w      │ v
    ∨        ∨        ∨
    C <───── T ─────> D
         h       k
```

[commutes](foundation-core.commuting-squares-of-maps.md).

The definition of morphisms of span diagrams is given concisely in terms of the
notion of morphisms of spans. In the resulting definitions, the commuting
squares of morphisms of spans are oriented in the following way:

- A homotopy
  `map-domain-hom-span ∘ left-map-span s ~ left-map-span t ∘ spanning-map-hom-span`
  witnessing that the square

  ```text
                       spanning-map-hom-span
                    S ──────────────────────> T
                    │                         │
    left-map-span s │                         │ left-map-span t
                    ∨                         ∨
                    A ──────────────────────> C
                        map-domain-hom-span
  ```

  commutes.

- A homotopy
  `map-domain-hom-span ∘ right-map-span s ~ right-map-span t ∘ spanning-map-hom-span`
  witnessing that the square

  ```text
                        spanning-map-hom-span
                     S ──────────────────────> T
                     │                         │
    right-map-span s │                         │ right-map-span t
                     ∨                         ∨
                     B ──────────────────────> D
                        map-codomain-hom-span
  ```

  commutes.

## Definitions

### Morphisms of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒮 : span-diagram l1 l2 l3) (𝒯 : span-diagram l4 l5 l6)
  where

  hom-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  hom-span-diagram =
    Σ ( domain-span-diagram 𝒮 → domain-span-diagram 𝒯)
      ( λ f →
        Σ ( codomain-span-diagram 𝒮 → codomain-span-diagram 𝒯)
          ( λ g →
            hom-span
              ( concat-span
                ( span-span-diagram 𝒮)
                ( f)
                ( g))
              ( span-span-diagram 𝒯)))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒮 : span-diagram l1 l2 l3) (𝒯 : span-diagram l4 l5 l6)
  (f : hom-span-diagram 𝒮 𝒯)
  where

  map-domain-hom-span-diagram :
    domain-span-diagram 𝒮 → domain-span-diagram 𝒯
  map-domain-hom-span-diagram = pr1 f

  map-codomain-hom-span-diagram :
    codomain-span-diagram 𝒮 → codomain-span-diagram 𝒯
  map-codomain-hom-span-diagram = pr1 (pr2 f)

  hom-span-hom-span-diagram :
    hom-span
      ( concat-span
        ( span-span-diagram 𝒮)
        ( map-domain-hom-span-diagram)
        ( map-codomain-hom-span-diagram))
      ( span-span-diagram 𝒯)
  hom-span-hom-span-diagram = pr2 (pr2 f)

  spanning-map-hom-span-diagram :
    spanning-type-span-diagram 𝒮 → spanning-type-span-diagram 𝒯
  spanning-map-hom-span-diagram =
    map-hom-span
      ( concat-span
        ( span-span-diagram 𝒮)
        ( map-domain-hom-span-diagram)
        ( map-codomain-hom-span-diagram))
      ( span-span-diagram 𝒯)
      ( hom-span-hom-span-diagram)

  left-square-hom-span-diagram :
    coherence-square-maps
      ( spanning-map-hom-span-diagram)
      ( left-map-span-diagram 𝒮)
      ( left-map-span-diagram 𝒯)
      ( map-domain-hom-span-diagram)
  left-square-hom-span-diagram =
    left-triangle-hom-span
      ( concat-span
        ( span-span-diagram 𝒮)
        ( map-domain-hom-span-diagram)
        ( map-codomain-hom-span-diagram))
      ( span-span-diagram 𝒯)
      ( hom-span-hom-span-diagram)

  left-hom-arrow-hom-span-diagram :
    hom-arrow (left-map-span-diagram 𝒮) (left-map-span-diagram 𝒯)
  pr1 left-hom-arrow-hom-span-diagram =
    spanning-map-hom-span-diagram
  pr1 (pr2 left-hom-arrow-hom-span-diagram) =
    map-domain-hom-span-diagram
  pr2 (pr2 left-hom-arrow-hom-span-diagram) =
    left-square-hom-span-diagram

  right-square-hom-span-diagram :
    coherence-square-maps
      ( spanning-map-hom-span-diagram)
      ( right-map-span-diagram 𝒮)
      ( right-map-span-diagram 𝒯)
      ( map-codomain-hom-span-diagram)
  right-square-hom-span-diagram =
    right-triangle-hom-span
      ( concat-span
        ( span-span-diagram 𝒮)
        ( map-domain-hom-span-diagram)
        ( map-codomain-hom-span-diagram))
      ( span-span-diagram 𝒯)
      ( hom-span-hom-span-diagram)

  right-hom-arrow-hom-span-diagram :
    hom-arrow (right-map-span-diagram 𝒮) (right-map-span-diagram 𝒯)
  pr1 right-hom-arrow-hom-span-diagram =
    spanning-map-hom-span-diagram
  pr1 (pr2 right-hom-arrow-hom-span-diagram) =
    map-codomain-hom-span-diagram
  pr2 (pr2 right-hom-arrow-hom-span-diagram) =
    right-square-hom-span-diagram
```
