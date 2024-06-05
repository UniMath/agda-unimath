# Descent data for pushouts

```agda
module synthetic-homotopy-theory.descent-data-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

{{#concept "Descent data" Disambiguation="pushouts" Agda=descent-data-pushout WDID=NA}}
for the [pushout](synthetic-homotopy-theory.universal-property-pushouts.md) of a
[span diagram](foundation.span-diagrams.md) `𝒮`

```text
     f     g
  A <-- S --> B
```

is a triple `(PA, PB, PS)`, where `PA : A → 𝒰` is a type family over `A`,
`PB : B → 𝒰` is a type family over `B`, and `PS` is a family of
[equivalences](foundation-core.equivalences.md)

```text
  PS : (s : S) → PA (f a) ≃ PB (g a).
```

In
[`descent-property-pushouts`](synthetic-homotopy-theory.descent-property-pushouts.md),
we show that this is exactly the data one needs to "glue together" a type family
`P : X → 𝒰` over the pushout `X` of `𝒮`.

The [identity type](foundation-core.identity-types.md) of descent data is
characterized in
[`equivalences-descent-data-pushouts`](synthetic-homotopy-theory.equivalences-descent-data-pushouts.md).

It may not be immediately clear why "descent data" is an appropriate name for
this concept, because there is no apparent downward motion. Traditionally,
descent is studied in the context of a collection of objects `Xᵢ` covering a
single object `X`, and local structure on the individual `Xᵢ`'s descending onto
`X`, collecting into a global structure, given that the pieces are appropriately
compatible on any "overlaps". A pushout of `𝒮` is covered by `A` and `B`, and
the overlaps are encoded in `f` and `g`. Then structure on `A` and `B`,
expressed as type families `PA` and `PB`, "descends" to a structure on `X` (a
type family over `X`). Two elements "overlap" in `X` if there is an
identification between them coming from `S`, and the gluing/compatibility
condition exactly requires the local structure of `PA` and `PB` to agree on such
elements, i.e. asks for an equivalence `PA(fs) ≃ PB(gs)`.

## Definitions

### Descent data for pushouts

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  descent-data-pushout : (l4 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
  descent-data-pushout l =
    Σ ( domain-span-diagram 𝒮 → UU l)
      ( λ PA →
        Σ ( codomain-span-diagram 𝒮 → UU l)
          ( λ PB →
            (s : spanning-type-span-diagram 𝒮) →
            PA (left-map-span-diagram 𝒮 s) ≃ PB (right-map-span-diagram 𝒮 s)))
```

### Components of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4)
  where

  left-family-descent-data-pushout : domain-span-diagram 𝒮 → UU l4
  left-family-descent-data-pushout = pr1 P

  right-family-descent-data-pushout : codomain-span-diagram 𝒮 → UU l4
  right-family-descent-data-pushout = pr1 (pr2 P)

  equiv-family-descent-data-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    left-family-descent-data-pushout (left-map-span-diagram 𝒮 s) ≃
    right-family-descent-data-pushout (right-map-span-diagram 𝒮 s)
  equiv-family-descent-data-pushout = pr2 (pr2 P)

  map-family-descent-data-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    left-family-descent-data-pushout (left-map-span-diagram 𝒮 s) →
    right-family-descent-data-pushout (right-map-span-diagram 𝒮 s)
  map-family-descent-data-pushout s =
    map-equiv (equiv-family-descent-data-pushout s)

  inv-map-family-descent-data-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    right-family-descent-data-pushout (right-map-span-diagram 𝒮 s) →
    left-family-descent-data-pushout (left-map-span-diagram 𝒮 s)
  inv-map-family-descent-data-pushout s =
    map-inv-equiv (equiv-family-descent-data-pushout s)

  is-equiv-map-family-descent-data-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    is-equiv (map-family-descent-data-pushout s)
  is-equiv-map-family-descent-data-pushout s =
    is-equiv-map-equiv (equiv-family-descent-data-pushout s)
```

### Descent data induced by families over cocones

Given a [cocone](synthetic-homotopy-theory.cocones-under-spans.md)

```text
        g
    S -----> B
    |        |
  f |        | j
    ∨        ∨
    A -----> X
        i
```

and a family `P : X → 𝒰`, we can obtain `PA` and `PB` by precomposing with `i`
and `j`, respectively. Then to produce an equivalence
`PS s : P (ifs) ≃ P (jgs)`, we
[transport](foundation-core.transport-along-identifications.md) along the
coherence `H s : ifs = jgs`, which is an equivalence.

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  descent-data-family-cocone-span-diagram :
    {l5 : Level} → (X → UU l5) → descent-data-pushout 𝒮 l5
  pr1 (descent-data-family-cocone-span-diagram P) =
    P ∘ horizontal-map-cocone _ _ c
  pr1 (pr2 (descent-data-family-cocone-span-diagram P)) =
    P ∘ vertical-map-cocone _ _ c
  pr2 (pr2 (descent-data-family-cocone-span-diagram P)) s =
    equiv-tr P (coherence-square-cocone _ _ c s)
```
