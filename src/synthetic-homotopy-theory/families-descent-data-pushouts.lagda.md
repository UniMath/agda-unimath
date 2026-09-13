# Families with descent data for pushouts

```agda
module synthetic-homotopy-theory.families-descent-data-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
```

</details>

## Idea

In [`descent-pushouts`](synthetic-homotopy-theory.descent-pushouts.md) we show
that given [descent data](synthetic-homotopy-theory.descent-data-pushouts.md)
`(PA, PB, PS)` over a [span diagram](foundation.span-diagrams.md) `𝒮`, there is
a unique type family `P` over its
[pushout](synthetic-homotopy-theory.pushouts.md) such that its induced descent
data is
[equivalent](synthetic-homotopy-theory.equivalences-descent-data-pushouts.md) to
`(PA, PB, PS)`. When stating theorems, it is sometimes useful to parameterize
over a user-provided type family, descent data, and the appropriate equivalence,
even though we technically can contract away the equivalence and either of the
endpoints. We call such a triple `(P, (PA, PB, PS), e)` a
{{#concept "family with descent data" Disambiguation="pushouts" Agda=family-with-descent-data-pushout}},
and denote it `P ≈ (PA, PB, PS)`.

## Definitions

### Type families over a cocone equipped with corresponding descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  family-with-descent-data-pushout :
    (l5 l6 l7 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6 ⊔ lsuc l7)
  family-with-descent-data-pushout l5 l6 l7 =
    Σ ( X → UU l7)
      ( λ P →
        Σ ( descent-data-pushout 𝒮 l5 l6)
          ( λ Q →
            equiv-descent-data-pushout
              ( descent-data-family-cocone-span-diagram c P)
              ( Q)))
```

### Components of a family with corresponding descent data

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5 l6 l7)
  where

  family-cocone-family-with-descent-data-pushout : X → UU l7
  family-cocone-family-with-descent-data-pushout = pr1 P

  descent-data-family-with-descent-data-pushout : descent-data-pushout 𝒮 l5 l6
  descent-data-family-with-descent-data-pushout = pr1 (pr2 P)

  left-family-family-with-descent-data-pushout :
    domain-span-diagram 𝒮 → UU l5
  left-family-family-with-descent-data-pushout =
    left-family-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout)

  right-family-family-with-descent-data-pushout :
    codomain-span-diagram 𝒮 → UU l6
  right-family-family-with-descent-data-pushout =
    right-family-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout)

  equiv-family-family-with-descent-data-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    left-family-family-with-descent-data-pushout (left-map-span-diagram 𝒮 s) ≃
    right-family-family-with-descent-data-pushout (right-map-span-diagram 𝒮 s)
  equiv-family-family-with-descent-data-pushout =
    equiv-family-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout)

  map-family-family-with-descent-data-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    left-family-family-with-descent-data-pushout (left-map-span-diagram 𝒮 s) →
    right-family-family-with-descent-data-pushout (right-map-span-diagram 𝒮 s)
  map-family-family-with-descent-data-pushout =
    map-family-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout)

  equiv-descent-data-family-with-descent-data-pushout :
    equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
  equiv-descent-data-family-with-descent-data-pushout = pr2 (pr2 P)

  inv-equiv-descent-data-family-with-descent-data-pushout :
    equiv-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout)
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
  inv-equiv-descent-data-family-with-descent-data-pushout =
    inv-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
      ( equiv-descent-data-family-with-descent-data-pushout)

  left-equiv-family-with-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    family-cocone-family-with-descent-data-pushout
      ( horizontal-map-cocone _ _ c a) ≃
    left-family-family-with-descent-data-pushout a
  left-equiv-family-with-descent-data-pushout =
    left-equiv-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
      ( equiv-descent-data-family-with-descent-data-pushout)

  left-map-family-with-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    family-cocone-family-with-descent-data-pushout
      ( horizontal-map-cocone _ _ c a) →
    left-family-family-with-descent-data-pushout a
  left-map-family-with-descent-data-pushout =
    left-map-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
      ( equiv-descent-data-family-with-descent-data-pushout)

  is-equiv-left-map-family-with-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    is-equiv (left-map-family-with-descent-data-pushout a)
  is-equiv-left-map-family-with-descent-data-pushout =
    is-equiv-left-map-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
      ( equiv-descent-data-family-with-descent-data-pushout)

  inv-left-map-family-with-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    left-family-family-with-descent-data-pushout a →
    family-cocone-family-with-descent-data-pushout
      ( horizontal-map-cocone _ _ c a)
  inv-left-map-family-with-descent-data-pushout =
    inv-left-map-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
      ( equiv-descent-data-family-with-descent-data-pushout)

  right-equiv-family-with-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    family-cocone-family-with-descent-data-pushout
      ( vertical-map-cocone _ _ c b) ≃
    right-family-family-with-descent-data-pushout b
  right-equiv-family-with-descent-data-pushout =
    right-equiv-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
      ( equiv-descent-data-family-with-descent-data-pushout)

  right-map-family-with-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    family-cocone-family-with-descent-data-pushout
      ( vertical-map-cocone _ _ c b) →
    right-family-family-with-descent-data-pushout b
  right-map-family-with-descent-data-pushout =
    right-map-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
      ( equiv-descent-data-family-with-descent-data-pushout)

  is-equiv-right-map-family-with-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    is-equiv (right-map-family-with-descent-data-pushout b)
  is-equiv-right-map-family-with-descent-data-pushout =
    is-equiv-right-map-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
      ( equiv-descent-data-family-with-descent-data-pushout)

  inv-right-map-family-with-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    right-family-family-with-descent-data-pushout b →
    family-cocone-family-with-descent-data-pushout
      ( vertical-map-cocone _ _ c b)
  inv-right-map-family-with-descent-data-pushout =
    inv-right-map-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
      ( equiv-descent-data-family-with-descent-data-pushout)

  coherence-family-with-descent-data-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    coherence-square-maps
      ( left-map-family-with-descent-data-pushout
        ( left-map-span-diagram 𝒮 s))
      ( tr
        ( family-cocone-family-with-descent-data-pushout)
        ( coherence-square-cocone _ _ c s))
      ( map-family-family-with-descent-data-pushout s)
      ( right-map-family-with-descent-data-pushout (right-map-span-diagram 𝒮 s))
  coherence-family-with-descent-data-pushout =
    coherence-equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout))
      ( descent-data-family-with-descent-data-pushout)
      ( equiv-descent-data-family-with-descent-data-pushout)
```

### Type family together with its induced descent data

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  family-with-descent-data-pushout-family-cocone :
    {l : Level} (P : X → UU l) → family-with-descent-data-pushout c l l l
  pr1 (family-with-descent-data-pushout-family-cocone P) =
    P
  pr1 (pr2 (family-with-descent-data-pushout-family-cocone P)) =
    descent-data-family-cocone-span-diagram c P
  pr2 (pr2 (family-with-descent-data-pushout-family-cocone P)) =
    id-equiv-descent-data-pushout (descent-data-family-cocone-span-diagram c P)
```
