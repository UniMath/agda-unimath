# Equifibered dependent span diagrams

```agda
module synthetic-homotopy-theory.equifibered-dependent-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.descent-data-pushouts
```

</details>

## Idea

Given a [span diagram](foundation.span-diagrams.md) `𝒮` of the form

```text
      f       g
  A <---- S ----> B,
```

a
{{#concept "equifibered dependent span diagram" Disambiguation="over a span diagram" Agda=equifibered-dependent-span-diagram}}
is a triple of type families `PA`, `PB`, `PS` over the vertices of `𝒮`,

```text
  𝒰       𝒱       𝒲
  ↑       ↑       ↑
  A <---- S ----> B,
```

together with families of equivalences `PS s ≃ PA (f s)` and `PS s ≃ PB (g s)`
for every `s : S`.

The [identity type](foundation-core.identity-types.md) of equifibered dependent
span diagrams is characterized in
[`equivalences-equifibered-dependent-span-diagrams`](synthetic-homotopy-theory.equivalences-equifibered-dependent-span-diagrams.md).

## Definitions

### Equifibered dependent span diagrams

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  equifibered-dependent-span-diagram :
    (l4 l5 l6 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ lsuc l6)
  equifibered-dependent-span-diagram l4 l5 l6 =
    Σ ( domain-span-diagram 𝒮 → UU l4)
      ( λ PA →
        Σ ( codomain-span-diagram 𝒮 → UU l5)
          ( λ PB →
            Σ ( spanning-type-span-diagram 𝒮 → UU l6)
              ( λ PS →
                ( (s : spanning-type-span-diagram 𝒮) →
                  PS s ≃ PA (left-map-span-diagram 𝒮 s)) ×
                ( (s : spanning-type-span-diagram 𝒮) →
                  PS s ≃ PB (right-map-span-diagram 𝒮 s)))))
```

### Components of equifibered dependent span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : equifibered-dependent-span-diagram 𝒮 l4 l5 l6)
  where

  left-family-equifibered-dependent-span-diagram :
    domain-span-diagram 𝒮 → UU l4
  left-family-equifibered-dependent-span-diagram =
    pr1 P

  right-family-equifibered-dependent-span-diagram :
    codomain-span-diagram 𝒮 → UU l5
  right-family-equifibered-dependent-span-diagram =
    pr1 (pr2 P)

  spanning-type-family-equifibered-dependent-span-diagram :
    spanning-type-span-diagram 𝒮 → UU l6
  spanning-type-family-equifibered-dependent-span-diagram =
    pr1 (pr2 (pr2 P))

  equiv-left-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    spanning-type-family-equifibered-dependent-span-diagram s ≃
    left-family-equifibered-dependent-span-diagram (left-map-span-diagram 𝒮 s)
  equiv-left-family-equifibered-dependent-span-diagram =
    pr1 (pr2 (pr2 (pr2 P)))

  equiv-right-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    spanning-type-family-equifibered-dependent-span-diagram s ≃
    right-family-equifibered-dependent-span-diagram (right-map-span-diagram 𝒮 s)
  equiv-right-family-equifibered-dependent-span-diagram =
    pr2 (pr2 (pr2 (pr2 P)))

  map-left-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    spanning-type-family-equifibered-dependent-span-diagram s →
    left-family-equifibered-dependent-span-diagram (left-map-span-diagram 𝒮 s)
  map-left-family-equifibered-dependent-span-diagram =
    map-equiv ∘ equiv-left-family-equifibered-dependent-span-diagram

  map-right-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    spanning-type-family-equifibered-dependent-span-diagram s →
    right-family-equifibered-dependent-span-diagram (right-map-span-diagram 𝒮 s)
  map-right-family-equifibered-dependent-span-diagram =
    map-equiv ∘ equiv-right-family-equifibered-dependent-span-diagram

  map-inv-left-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    left-family-equifibered-dependent-span-diagram (left-map-span-diagram 𝒮 s) →
    spanning-type-family-equifibered-dependent-span-diagram s
  map-inv-left-family-equifibered-dependent-span-diagram =
    map-inv-equiv ∘ equiv-left-family-equifibered-dependent-span-diagram

  map-inv-right-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    right-family-equifibered-dependent-span-diagram
      ( right-map-span-diagram 𝒮 s) →
    spanning-type-family-equifibered-dependent-span-diagram s
  map-inv-right-family-equifibered-dependent-span-diagram =
    map-inv-equiv ∘ equiv-right-family-equifibered-dependent-span-diagram

  is-equiv-map-left-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    is-equiv (map-left-family-equifibered-dependent-span-diagram s)
  is-equiv-map-left-family-equifibered-dependent-span-diagram s =
    is-equiv-map-equiv (equiv-left-family-equifibered-dependent-span-diagram s)

  is-equiv-map-right-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    is-equiv (map-right-family-equifibered-dependent-span-diagram s)
  is-equiv-map-right-family-equifibered-dependent-span-diagram s =
    is-equiv-map-equiv (equiv-right-family-equifibered-dependent-span-diagram s)

  equiv-left-right-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    left-family-equifibered-dependent-span-diagram (left-map-span-diagram 𝒮 s) ≃
    right-family-equifibered-dependent-span-diagram (right-map-span-diagram 𝒮 s)
  equiv-left-right-family-equifibered-dependent-span-diagram s =
    equiv-right-family-equifibered-dependent-span-diagram s ∘e
    inv-equiv (equiv-left-family-equifibered-dependent-span-diagram s)

  map-left-right-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    left-family-equifibered-dependent-span-diagram (left-map-span-diagram 𝒮 s) →
    right-family-equifibered-dependent-span-diagram (right-map-span-diagram 𝒮 s)
  map-left-right-family-equifibered-dependent-span-diagram =
    map-equiv ∘ equiv-left-right-family-equifibered-dependent-span-diagram

  equiv-right-left-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    right-family-equifibered-dependent-span-diagram
      ( right-map-span-diagram 𝒮 s) ≃
    left-family-equifibered-dependent-span-diagram
      ( left-map-span-diagram 𝒮 s)
  equiv-right-left-family-equifibered-dependent-span-diagram s =
    equiv-left-family-equifibered-dependent-span-diagram s ∘e
    inv-equiv (equiv-right-family-equifibered-dependent-span-diagram s)

  map-right-left-family-equifibered-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    right-family-equifibered-dependent-span-diagram
      ( right-map-span-diagram 𝒮 s) →
    left-family-equifibered-dependent-span-diagram
      ( left-map-span-diagram 𝒮 s)
  map-right-left-family-equifibered-dependent-span-diagram =
    map-equiv ∘ equiv-right-left-family-equifibered-dependent-span-diagram

  descent-data-pushout-equifibered-dependent-span-diagram :
    descent-data-pushout 𝒮 l4 l5
  descent-data-pushout-equifibered-dependent-span-diagram =
    ( left-family-equifibered-dependent-span-diagram ,
      right-family-equifibered-dependent-span-diagram ,
      equiv-left-right-family-equifibered-dependent-span-diagram)
```

### Equifibered dependent span diagrams induced by descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4 l5)
  where

  equifibered-dependent-span-diagram-descent-data-pushout :
    equifibered-dependent-span-diagram 𝒮 l4 l5 l4
  equifibered-dependent-span-diagram-descent-data-pushout =
    ( left-family-descent-data-pushout P) ,
    ( right-family-descent-data-pushout P) ,
    ( left-family-descent-data-pushout P ∘ left-map-span-diagram 𝒮) ,
    ( λ _ → id-equiv) ,
    ( equiv-family-descent-data-pushout P)
```

### Equifibered dependent span diagrams induced by families over cocones

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  equifibered-dependent-span-diagram-family-cocone-span-diagram :
    {l5 : Level} → (X → UU l5) → equifibered-dependent-span-diagram 𝒮 l5 l5 l5
  equifibered-dependent-span-diagram-family-cocone-span-diagram P =
    equifibered-dependent-span-diagram-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c P)
```

## See also

- [Descent data for pushouts](synthetic-homotopy-theory.descent-data-pushouts.md)
  is a variant of equifibered dependent span diagrams where a type family over
  the middle vertex is not specified.
