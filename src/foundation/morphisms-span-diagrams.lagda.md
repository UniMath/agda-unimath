# Morphisms of span diagrams

```agda
module foundation.morphisms-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.extensions-spans
open import foundation.morphisms-arrows
open import foundation.morphisms-spans
open import foundation.span-diagrams
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
```

</details>

## Idea

A {{#concept "morphism of span diagrams"}} from a
[span diagram](foundation.span-diagrams.md) `A <-f- S -g-> B` to
a span diagram `C <-h- T -k-> D` consists of maps `u : A → C`, `v : B → D`, and
`w : S → T` [equipped](foundation.structure.md) with two
[homotopies](foundation-core.homotopies.md) witnessing that the diagram

```text
         f       g
    A <----- S -----> B
    |        |        |
  u |        | w      | v
    V        V        V
    C <----- T -----> D
         h       k
```

[commutes](foundation-core.commuting-squares-of-maps.md).

The definition of morphisms of span diagrams is given concisely in terms of the notion
of morphisms of spans. In the resulting
definitions, the commuting squares of morphisms of spans are oriented in the
following way:

- A homotopy
  `map-domain-hom-span ∘ left-map-span s ~ left-map-span t ∘ spanning-map-hom-span`
  witnessing that the square

  ```text
                       spanning-map-hom-span
                    S ----------------------> T
                    |                         |
    left-map-span s |                         | left-map-span t
                    V                         V
                    A ----------------------> C
                        map-domain-hom-span
  ```

  commutes.

- A homotopy
  `map-domain-hom-span ∘ right-map-span s ~ right-map-span t ∘ spanning-map-hom-span`
  witnessing that the square

  ```text
                        spanning-map-hom-span
                     S ----------------------> T
                     |                         |
    right-map-span s |                         | right-map-span t
                     V                         V
                     B ----------------------> D
                        map-codomain-hom-span
  ```

  commutes.

## Definitions

### Morphisms of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (s : span-diagram l1 l2 l3) (t : span-diagram l4 l5 l6)
  where

  hom-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  hom-span-diagram =
    Σ ( domain-span-diagram s → domain-span-diagram t)
      ( λ f →
        Σ ( codomain-span-diagram s → codomain-span-diagram t)
          ( λ g →
            hom-span
              ( extend-span
                ( span-span-diagram s)
                ( f)
                ( g))
              ( span-span-diagram t)))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (s : span-diagram l1 l2 l3) (t : span-diagram l4 l5 l6)
  (f : hom-span-diagram s t)
  where

  map-domain-hom-span-diagram :
    domain-span-diagram s → domain-span-diagram t
  map-domain-hom-span-diagram = pr1 f

  map-codomain-hom-span-diagram :
    codomain-span-diagram s → codomain-span-diagram t
  map-codomain-hom-span-diagram = pr1 (pr2 f)

  hom-span-hom-span-diagram :
    hom-span
      ( extend-span
        ( span-span-diagram s)
        ( map-domain-hom-span-diagram)
        ( map-codomain-hom-span-diagram))
      ( span-span-diagram t)
  hom-span-hom-span-diagram = pr2 (pr2 f)

  spanning-map-hom-span-diagram :
    spanning-type-span-diagram s → spanning-type-span-diagram t
  spanning-map-hom-span-diagram =
    map-hom-span
      ( extend-span
        ( span-span-diagram s)
        ( map-domain-hom-span-diagram)
        ( map-codomain-hom-span-diagram))
      ( span-span-diagram t)
      ( hom-span-hom-span-diagram)

  left-square-hom-span-diagram :
    coherence-square-maps
      ( spanning-map-hom-span-diagram)
      ( left-map-span-diagram s)
      ( left-map-span-diagram t)
      ( map-domain-hom-span-diagram)
  left-square-hom-span-diagram =
    left-triangle-hom-span
      ( extend-span
        ( span-span-diagram s)
        ( map-domain-hom-span-diagram)
        ( map-codomain-hom-span-diagram))
      ( span-span-diagram t)
      ( hom-span-hom-span-diagram)

  left-hom-arrow-hom-span-diagram :
    hom-arrow (left-map-span-diagram s) (left-map-span-diagram t)
  pr1 left-hom-arrow-hom-span-diagram =
    spanning-map-hom-span-diagram
  pr1 (pr2 left-hom-arrow-hom-span-diagram) =
    map-domain-hom-span-diagram
  pr2 (pr2 left-hom-arrow-hom-span-diagram) =
    left-square-hom-span-diagram

  right-square-hom-span-diagram :
    coherence-square-maps
      ( spanning-map-hom-span-diagram)
      ( right-map-span-diagram s)
      ( right-map-span-diagram t)
      ( map-codomain-hom-span-diagram)
  right-square-hom-span-diagram =
    right-triangle-hom-span
      ( extend-span
        ( span-span-diagram s)
        ( map-domain-hom-span-diagram)
        ( map-codomain-hom-span-diagram))
      ( span-span-diagram t)
      ( hom-span-hom-span-diagram)

  right-hom-arrow-hom-span-diagram :
    hom-arrow (right-map-span-diagram s) (right-map-span-diagram t)
  pr1 right-hom-arrow-hom-span-diagram =
    spanning-map-hom-span-diagram
  pr1 (pr2 right-hom-arrow-hom-span-diagram) =
    map-codomain-hom-span-diagram
  pr2 (pr2 right-hom-arrow-hom-span-diagram) =
    right-square-hom-span-diagram
```

