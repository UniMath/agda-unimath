# Descent for pushouts

```agda
module synthetic-homotopy-theory.descent-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-contractible-types
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The
{{#concept "descent property" Disambiguation="of pushouts" Agda=uniqueness-family-cocone-descent-data-pushout WDID=Q5263725 WD="descent"}}
of [pushouts](synthetic-homotopy-theory.pushouts.md) states that given a pushout

```text
        g
    S -----> B
    |        |
  f |        | j
    ∨        ∨
    A -----> X,
        i
```

there is an [equivalence](foundation-core.equivalences.md) between the type of
type families `X → 𝒰` and the type of
[descent data](synthetic-homotopy-theory.descent-data-pushouts.md) for the span.

**Proof:** We observe that there is a commuting triangle

```text
           cocone-map
  (X → 𝒰) -----------> cocone 𝒰
         \             /
           \         /
             ∨     ∨
          descent-data.
```

The left map constructs descent data out of a type family by precomposing the
cocone legs and transporting along the commuting square, as defined in
[`descent-data-pushouts`](synthetic-homotopy-theory.descent-data-pushouts.md).
The right map takes a cocone `(PA, PB, K)` to the descent data where the
equivalences `PA(fs) ≃ PB(gs)` are obtained from the
[identifications](foundation-core.identity-types.md) `K s : PA(fs) = PB(gs)`.

The top map is an equivalence by assumption, since we assume that the cocone is
a pushout, and the right map is an equivalence by
[univalence](foundation-core.univalence.md). It follows that the left map is an
equivalence by the 3-for-2 property of equivalences.

Instead of only stating that there is such an equivalence, we show a uniqueness
property: for any descent data `(PA, PB, PS)`, the type of type families
`P : X → 𝒰` equipped with an
[equivalence of descent data](synthetic-homotopy-theory.equivalences-descent-data-pushouts.md)
`(P ∘ i, P ∘ j, λ s → tr P (H s)) ≃ (PA, PB, PS)` is
[contractible](foundation-core.contractible-types.md). In other words, there is
a unique type family `P : X → 𝒰` such that there are equivalences

```text
  eA : (a : A) → P(ia) ≃ PA a
  eB : (b : B) → P(jb) ≃ PB b
```

and the square

```text
           eA (fs)
  P(ifs) --------> PA(fs)
     |                 |
     | tr P (H s)      | PS s
     |                 |
     ∨                 ∨
  P(jgs) --------> PB(gs)
           eB (gs)
```

[commutes](foundation-core.commuting-squares-of-maps.md) for all `s : S`.

**Proof:** The map sending type families over `X` to descent data is an
equivalence, hence it is a
[contractible map](foundation-core.contractible-maps.md). The contractible fiber
at `(PA, PB, PS)` is the type of type families `P : X → 𝒰` equipped with an
identification `(P ∘ i, P ∘ j, λ s → tr P (H s)) = (PA, PB, PS)`, and the type
of such identifications is equivalent to the type of equivalences of descent
data.

## Theorem

```agda
module _
  {l1 l2 l3 : Level} {𝒮 : span-diagram l1 l2 l3}
  where

  equiv-descent-data-cocone-span-diagram-UU :
    (l4 : Level) →
    cocone-span-diagram 𝒮 (UU l4) ≃
    descent-data-pushout 𝒮 l4 l4
  equiv-descent-data-cocone-span-diagram-UU _ =
    equiv-tot
      ( λ PA →
        equiv-tot (λ PB → (equiv-Π-equiv-family (λ s → equiv-univalence))))

  descent-data-cocone-span-diagram-UU :
    {l4 : Level} →
    cocone-span-diagram 𝒮 (UU l4) →
    descent-data-pushout 𝒮 l4 l4
  descent-data-cocone-span-diagram-UU {l4} =
    map-equiv (equiv-descent-data-cocone-span-diagram-UU l4)

  is-equiv-descent-data-cocone-span-diagram-UU :
    {l4 : Level} → is-equiv (descent-data-cocone-span-diagram-UU {l4})
  is-equiv-descent-data-cocone-span-diagram-UU {l4} =
    is-equiv-map-equiv (equiv-descent-data-cocone-span-diagram-UU l4)

module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  triangle-descent-data-family-cocone-span-diagram :
    {l5 : Level} →
    coherence-triangle-maps
      ( descent-data-family-cocone-span-diagram c)
      ( descent-data-cocone-span-diagram-UU {l4 = l5})
      ( cocone-map-span-diagram c)
  triangle-descent-data-family-cocone-span-diagram P =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( eq-htpy
          ( λ s → inv (compute-equiv-eq-ap (coherence-square-cocone _ _ c s)))))

module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  where

  is-equiv-descent-data-family-cocone-span-diagram :
    {l5 : Level} →
    is-equiv (descent-data-family-cocone-span-diagram c {l5})
  is-equiv-descent-data-family-cocone-span-diagram {l5} =
    is-equiv-left-map-triangle _ _ _
      ( triangle-descent-data-family-cocone-span-diagram c)
      ( up-c (UU l5))
      ( is-equiv-descent-data-cocone-span-diagram-UU)

module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (P : descent-data-pushout 𝒮 l5 l5)
  where

  abstract
    uniqueness-family-cocone-descent-data-pushout :
      is-contr
        ( Σ ( X → UU l5)
            ( λ Q →
              equiv-descent-data-pushout
                ( descent-data-family-cocone-span-diagram c Q)
                ( P)))
    uniqueness-family-cocone-descent-data-pushout =
      is-contr-equiv'
        ( fiber (descent-data-family-cocone-span-diagram c) P)
        ( equiv-tot
          ( λ Q →
            extensionality-descent-data-pushout
              ( descent-data-family-cocone-span-diagram c Q)
              ( P)))
        ( is-contr-map-is-equiv
          ( is-equiv-descent-data-family-cocone-span-diagram up-c)
          ( P))

  family-cocone-descent-data-pushout : X → UU l5
  family-cocone-descent-data-pushout =
    pr1 (center uniqueness-family-cocone-descent-data-pushout)

  equiv-family-cocone-descent-data-pushout :
    equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-descent-data-pushout))
      ( P)
  equiv-family-cocone-descent-data-pushout =
    pr2 (center uniqueness-family-cocone-descent-data-pushout)

  compute-left-family-cocone-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    family-cocone-descent-data-pushout (horizontal-map-cocone _ _ c a) ≃
    left-family-descent-data-pushout P a
  compute-left-family-cocone-descent-data-pushout =
    left-equiv-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-descent-data-pushout))
      ( P)
      ( equiv-family-cocone-descent-data-pushout)

  map-compute-left-family-cocone-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    family-cocone-descent-data-pushout (horizontal-map-cocone _ _ c a) →
    left-family-descent-data-pushout P a
  map-compute-left-family-cocone-descent-data-pushout a =
    map-equiv (compute-left-family-cocone-descent-data-pushout a)

  compute-right-family-cocone-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    family-cocone-descent-data-pushout (vertical-map-cocone _ _ c b) ≃
    right-family-descent-data-pushout P b
  compute-right-family-cocone-descent-data-pushout =
    right-equiv-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-descent-data-pushout))
      ( P)
      ( equiv-family-cocone-descent-data-pushout)

  map-compute-right-family-cocone-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    family-cocone-descent-data-pushout (vertical-map-cocone _ _ c b) →
    right-family-descent-data-pushout P b
  map-compute-right-family-cocone-descent-data-pushout b =
    map-equiv (compute-right-family-cocone-descent-data-pushout b)

  inv-equiv-family-cocone-descent-data-pushout :
    equiv-descent-data-pushout P
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-descent-data-pushout))
  inv-equiv-family-cocone-descent-data-pushout =
    inv-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-descent-data-pushout))
      ( P)
      ( equiv-family-cocone-descent-data-pushout)

  compute-inv-left-family-cocone-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    left-family-descent-data-pushout P a ≃
    family-cocone-descent-data-pushout (horizontal-map-cocone _ _ c a)
  compute-inv-left-family-cocone-descent-data-pushout =
    left-equiv-equiv-descent-data-pushout P
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-descent-data-pushout))
      ( inv-equiv-family-cocone-descent-data-pushout)

  map-compute-inv-left-family-cocone-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    left-family-descent-data-pushout P a →
    family-cocone-descent-data-pushout (horizontal-map-cocone _ _ c a)
  map-compute-inv-left-family-cocone-descent-data-pushout a =
    map-equiv (compute-inv-left-family-cocone-descent-data-pushout a)

  compute-inv-right-family-cocone-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    right-family-descent-data-pushout P b ≃
    family-cocone-descent-data-pushout (vertical-map-cocone _ _ c b)
  compute-inv-right-family-cocone-descent-data-pushout =
    right-equiv-equiv-descent-data-pushout P
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-descent-data-pushout))
      ( inv-equiv-family-cocone-descent-data-pushout)

  map-compute-inv-right-family-cocone-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    right-family-descent-data-pushout P b →
    family-cocone-descent-data-pushout (vertical-map-cocone _ _ c b)
  map-compute-inv-right-family-cocone-descent-data-pushout b =
    map-equiv (compute-inv-right-family-cocone-descent-data-pushout b)

  family-with-descent-data-pushout-descent-data-pushout :
    family-with-descent-data-pushout c l5 l5 l5
  pr1 family-with-descent-data-pushout-descent-data-pushout =
    family-cocone-descent-data-pushout
  pr1 (pr2 family-with-descent-data-pushout-descent-data-pushout) =
    P
  pr2 (pr2 family-with-descent-data-pushout-descent-data-pushout) =
    equiv-family-cocone-descent-data-pushout
```

## Table of descent properties

{{#include tables/descent-properties.md}}
