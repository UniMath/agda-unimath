# Morphisms of spans

```agda
module foundation.morphisms-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
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
[span](foundation.spans) `A <-f- S -g-> B` to a span `A <-h- T -k-> B` consists
of a map `w : S → T` [equipped](foundation.structure.md) with two
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
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2}
  where

  coherence-hom-spanning-type-span-fixed-domain-codomain :
    (c d : span-fixed-domain-codomain l A B) →
    ( spanning-type-span-fixed-domain-codomain c →
      spanning-type-span-fixed-domain-codomain d) →
    UU (l1 ⊔ l2 ⊔ l)
  coherence-hom-spanning-type-span-fixed-domain-codomain c d h =
    ( coherence-triangle-maps
      ( left-map-span-fixed-domain-codomain c)
      ( left-map-span-fixed-domain-codomain d)
      ( h)) ×
    ( coherence-triangle-maps
      ( right-map-span-fixed-domain-codomain c)
      ( right-map-span-fixed-domain-codomain d)
      ( h))

  hom-spanning-type-span-fixed-domain-codomain :
    ( c d : span-fixed-domain-codomain l A B) → UU (l1 ⊔ l2 ⊔ l)
  hom-spanning-type-span-fixed-domain-codomain c d =
    Σ ( spanning-type-span-fixed-domain-codomain c →
        spanning-type-span-fixed-domain-codomain d)
      ( coherence-hom-spanning-type-span-fixed-domain-codomain c d)
```
