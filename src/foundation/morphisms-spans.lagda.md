# Morphisms of spans

```agda
module foundation.morphisms-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.spans
open import foundation.universe-levels
```

</details>

## Idea

We consider four concepts of morphisms between spans, according to our different
concepts of spans:

- Morphisms of (binary) spans with fixed domain and codomain.
- Morphisms of (binary) spans.
- Morphisms of spans of a fixed family of types.
- Morphisms of spans of families of types indexed by a fixed indexing type.

### Morphisms of binary spans with fixed domain and codomain

A **morphism of spans with fixed domain and codomain** from a
[span](foundation.spans.md) `A <-f- S -g-> B` to a span `A <-h- T -k-> B`
consists of a map `w : S → T` [equipped](foundation.structure.md) with two
[homotopies](foundation-core.homotopies.md) witnessing that the diagram

```text
             S
           / | \
        f /  |  \ h
         V   |   V
        A    |w   B
         ∧   |   ∧
        h \  |  / k
           \ V /
             T
```

[commutes](foundation.commuting-squares-of-maps.md).

### Morphisms of binary spans

A **morphism of spans** from a [span](foundation.spans.md) `A <-f- S -g-> B` to
a span `C <-h- T -k-> D` consists of maps `u : A → C`, `v : B → D`, and
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

commutes.

### Morphisms of spans of families of types

The notion of **morphism of spans of (fixed) families of types** is the natural
generalization of the notion of morphisms of (fixed) families of types.

## Definitions

### Morphisms between (binary) spans with fixed domain and codomain

The notion of morphism of spans `c` and `d` with fixed domain and codomain is a
map between their domains so that the triangles on either side commute:

```text
  A ===== A
  ∧       ∧
  |       |
  C ----> D
  |       |
  v       v
  B ===== B
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : span-fixed-domain-codomain l3 A B)
  (t : span-fixed-domain-codomain l4 A B)
  where

  left-coherence-hom-span-fixed-domain-codomain :
    ( spanning-type-span-fixed-domain-codomain s →
      spanning-type-span-fixed-domain-codomain t) →
    UU (l1 ⊔ l3)
  left-coherence-hom-span-fixed-domain-codomain =
    coherence-triangle-maps
      ( left-map-span-fixed-domain-codomain s)
      ( left-map-span-fixed-domain-codomain t)

  right-coherence-hom-span-fixed-domain-codomain :
    ( spanning-type-span-fixed-domain-codomain s →
      spanning-type-span-fixed-domain-codomain t) →
    UU (l2 ⊔ l3)
  right-coherence-hom-span-fixed-domain-codomain =
    coherence-triangle-maps
      ( right-map-span-fixed-domain-codomain s)
      ( right-map-span-fixed-domain-codomain t)

  coherence-hom-span-fixed-domain-codomain :
    ( spanning-type-span-fixed-domain-codomain s →
      spanning-type-span-fixed-domain-codomain t) →
    UU (l1 ⊔ l2 ⊔ l3)
  coherence-hom-span-fixed-domain-codomain f =
    left-coherence-hom-span-fixed-domain-codomain f ×
    right-coherence-hom-span-fixed-domain-codomain f

  hom-span-fixed-domain-codomain : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-span-fixed-domain-codomain =
    Σ ( spanning-type-span-fixed-domain-codomain s →
        spanning-type-span-fixed-domain-codomain t)
      ( coherence-hom-span-fixed-domain-codomain)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : span-fixed-domain-codomain l3 A B)
  (t : span-fixed-domain-codomain l4 A B)
  (f : hom-span-fixed-domain-codomain s t)
  where

  map-hom-span-fixed-domain-codomain :
    spanning-type-span-fixed-domain-codomain s →
    spanning-type-span-fixed-domain-codomain t
  map-hom-span-fixed-domain-codomain = pr1 f

  left-triangle-hom-span-fixed-domain-codomain :
    left-coherence-hom-span-fixed-domain-codomain s t
      ( map-hom-span-fixed-domain-codomain)
  left-triangle-hom-span-fixed-domain-codomain = pr1 (pr2 f)

  right-triangle-hom-span-fixed-domain-codomain :
    right-coherence-hom-span-fixed-domain-codomain s t
      ( map-hom-span-fixed-domain-codomain)
  right-triangle-hom-span-fixed-domain-codomain = pr2 (pr2 f)
```

### Morphisms of spans

The definition of morphisms of spans is given concisely in terms of the notion
of morphisms of spans with fixed domain and codomain. In the resulting
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

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3) (t : span l4 l5 l6)
  where

  hom-span : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  hom-span =
    Σ ( domain-span s → domain-span t)
      ( λ f →
        Σ ( codomain-span s → codomain-span t)
          ( λ g →
            hom-span-fixed-domain-codomain
              ( extend-span-fixed-domain-codomain
                ( span-fixed-domain-codomain-span s)
                ( f)
                ( g))
              ( span-fixed-domain-codomain-span t)))

module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3) (t : span l4 l5 l6)
  (f : hom-span s t)
  where

  map-domain-hom-span :
    domain-span s → domain-span t
  map-domain-hom-span = pr1 f

  map-codomain-hom-span :
    codomain-span s → codomain-span t
  map-codomain-hom-span = pr1 (pr2 f)

  hom-span-fixed-domain-codomain-hom-span :
    hom-span-fixed-domain-codomain
      ( extend-span-fixed-domain-codomain
        ( span-fixed-domain-codomain-span s)
        ( map-domain-hom-span)
        ( map-codomain-hom-span))
      ( span-fixed-domain-codomain-span t)
  hom-span-fixed-domain-codomain-hom-span = pr2 (pr2 f)

  spanning-map-hom-span :
    spanning-type-span s → spanning-type-span t
  spanning-map-hom-span =
    map-hom-span-fixed-domain-codomain
      ( extend-span-fixed-domain-codomain
        ( span-fixed-domain-codomain-span s)
        ( map-domain-hom-span)
        ( map-codomain-hom-span))
      ( span-fixed-domain-codomain-span t)
      ( hom-span-fixed-domain-codomain-hom-span)

  left-square-hom-span :
    coherence-square-maps
      ( spanning-map-hom-span)
      ( left-map-span s)
      ( left-map-span t)
      ( map-domain-hom-span)
  left-square-hom-span =
    left-triangle-hom-span-fixed-domain-codomain
      ( extend-span-fixed-domain-codomain
        ( span-fixed-domain-codomain-span s)
        ( map-domain-hom-span)
        ( map-codomain-hom-span))
      ( span-fixed-domain-codomain-span t)
      ( hom-span-fixed-domain-codomain-hom-span)

  right-square-hom-span :
    coherence-square-maps
      ( spanning-map-hom-span)
      ( right-map-span s)
      ( right-map-span t)
      ( map-codomain-hom-span)
  right-square-hom-span =
    right-triangle-hom-span-fixed-domain-codomain
      ( extend-span-fixed-domain-codomain
        ( span-fixed-domain-codomain-span s)
        ( map-domain-hom-span)
        ( map-codomain-hom-span))
      ( span-fixed-domain-codomain-span t)
      ( hom-span-fixed-domain-codomain-hom-span)
```
