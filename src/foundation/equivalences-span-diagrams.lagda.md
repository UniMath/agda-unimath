# Equivalences of span diagrams

```agda
module foundation.equivalences-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.equivalences-spans
open import foundation.fundamental-theorem-of-identity-types
open import foundation.morphisms-span-diagrams
open import foundation.morphisms-spans
open import foundation.operations-spans
open import foundation.propositions
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences-arrows
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An {{#concept "equivalence of span diagrams" Agda=equiv-span-diagram}} from a
[span diagram](foundation.span-diagrams.md) `A <-f- S -g-> B` to a span diagram
`C <-h- T -k-> D` consists of [equivalences](foundation-core.equivalences.md)
`u : A ≃ C`, `v : B ≃ D`, and `w : S ≃ T` [equipped](foundation.structure.md)
with two [homotopies](foundation-core.homotopies.md) witnessing that the diagram

```text
         f       g
    A <----- S -----> B
    |        |        |
  u |        | w      | v
    ∨        ∨        ∨
    C <----- T -----> D
         h       k
```

[commutes](foundation-core.commuting-squares-of-maps.md).

## Definitions

### The predicate of being an equivalence of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒮 : span-diagram l1 l2 l3) (𝒯 : span-diagram l4 l5 l6)
  (f : hom-span-diagram 𝒮 𝒯)
  where

  is-equiv-prop-hom-span-diagram : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-equiv-prop-hom-span-diagram =
    product-Prop
      ( is-equiv-Prop (map-domain-hom-span-diagram 𝒮 𝒯 f))
      ( product-Prop
        ( is-equiv-Prop (map-codomain-hom-span-diagram 𝒮 𝒯 f))
        ( is-equiv-Prop (spanning-map-hom-span-diagram 𝒮 𝒯 f)))

  is-equiv-hom-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-equiv-hom-span-diagram = type-Prop is-equiv-prop-hom-span-diagram

  is-prop-is-equiv-hom-span-diagram : is-prop is-equiv-hom-span-diagram
  is-prop-is-equiv-hom-span-diagram =
    is-prop-type-Prop is-equiv-prop-hom-span-diagram
```

### Equivalences of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒮 : span-diagram l1 l2 l3) (𝒯 : span-diagram l4 l5 l6)
  where

  equiv-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  equiv-span-diagram =
    Σ ( domain-span-diagram 𝒮 ≃ domain-span-diagram 𝒯)
      ( λ e →
        Σ ( codomain-span-diagram 𝒮 ≃ codomain-span-diagram 𝒯)
          ( λ f →
            equiv-span
              ( concat-span (span-span-diagram 𝒮) (map-equiv e) (map-equiv f))
              ( span-span-diagram 𝒯)))

  module _
    (e : equiv-span-diagram)
    where

    equiv-domain-equiv-span-diagram :
      domain-span-diagram 𝒮 ≃ domain-span-diagram 𝒯
    equiv-domain-equiv-span-diagram = pr1 e

    map-domain-equiv-span-diagram :
      domain-span-diagram 𝒮 → domain-span-diagram 𝒯
    map-domain-equiv-span-diagram = map-equiv equiv-domain-equiv-span-diagram

    is-equiv-map-domain-equiv-span-diagram :
      is-equiv map-domain-equiv-span-diagram
    is-equiv-map-domain-equiv-span-diagram =
      is-equiv-map-equiv equiv-domain-equiv-span-diagram

    equiv-codomain-equiv-span-diagram :
      codomain-span-diagram 𝒮 ≃ codomain-span-diagram 𝒯
    equiv-codomain-equiv-span-diagram = pr1 (pr2 e)

    map-codomain-equiv-span-diagram :
      codomain-span-diagram 𝒮 → codomain-span-diagram 𝒯
    map-codomain-equiv-span-diagram =
      map-equiv equiv-codomain-equiv-span-diagram

    is-equiv-map-codomain-equiv-span-diagram :
      is-equiv map-codomain-equiv-span-diagram
    is-equiv-map-codomain-equiv-span-diagram =
      is-equiv-map-equiv equiv-codomain-equiv-span-diagram

    equiv-span-equiv-span-diagram :
      equiv-span
        ( concat-span
          ( span-span-diagram 𝒮)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram 𝒯)
    equiv-span-equiv-span-diagram =
      pr2 (pr2 e)

    spanning-equiv-equiv-span-diagram :
      spanning-type-span-diagram 𝒮 ≃ spanning-type-span-diagram 𝒯
    spanning-equiv-equiv-span-diagram =
      equiv-equiv-span
        ( concat-span
          ( span-span-diagram 𝒮)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram 𝒯)
        ( equiv-span-equiv-span-diagram)

    spanning-map-equiv-span-diagram :
      spanning-type-span-diagram 𝒮 → spanning-type-span-diagram 𝒯
    spanning-map-equiv-span-diagram =
      map-equiv-span
        ( concat-span
          ( span-span-diagram 𝒮)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram 𝒯)
        ( equiv-span-equiv-span-diagram)

    is-equiv-spanning-map-equiv-span-diagram :
      is-equiv spanning-map-equiv-span-diagram
    is-equiv-spanning-map-equiv-span-diagram =
      is-equiv-equiv-span
        ( concat-span
          ( span-span-diagram 𝒮)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram 𝒯)
        ( equiv-span-equiv-span-diagram)

    left-square-equiv-span-diagram :
      coherence-square-maps
        ( spanning-map-equiv-span-diagram)
        ( left-map-span-diagram 𝒮)
        ( left-map-span-diagram 𝒯)
        ( map-domain-equiv-span-diagram)
    left-square-equiv-span-diagram =
      left-triangle-equiv-span
        ( concat-span
          ( span-span-diagram 𝒮)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram 𝒯)
        ( equiv-span-equiv-span-diagram)

    equiv-left-arrow-equiv-span-diagram :
      equiv-arrow (left-map-span-diagram 𝒮) (left-map-span-diagram 𝒯)
    pr1 equiv-left-arrow-equiv-span-diagram =
      spanning-equiv-equiv-span-diagram
    pr1 (pr2 equiv-left-arrow-equiv-span-diagram) =
      equiv-domain-equiv-span-diagram
    pr2 (pr2 equiv-left-arrow-equiv-span-diagram) =
      left-square-equiv-span-diagram

    right-square-equiv-span-diagram :
      coherence-square-maps
        ( spanning-map-equiv-span-diagram)
        ( right-map-span-diagram 𝒮)
        ( right-map-span-diagram 𝒯)
        ( map-codomain-equiv-span-diagram)
    right-square-equiv-span-diagram =
      right-triangle-equiv-span
        ( concat-span
          ( span-span-diagram 𝒮)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram 𝒯)
        ( equiv-span-equiv-span-diagram)

    equiv-right-arrow-equiv-span-diagram :
      equiv-arrow (right-map-span-diagram 𝒮) (right-map-span-diagram 𝒯)
    pr1 equiv-right-arrow-equiv-span-diagram =
      spanning-equiv-equiv-span-diagram
    pr1 (pr2 equiv-right-arrow-equiv-span-diagram) =
      equiv-codomain-equiv-span-diagram
    pr2 (pr2 equiv-right-arrow-equiv-span-diagram) =
      right-square-equiv-span-diagram

    hom-span-equiv-span-diagram :
      hom-span
        ( concat-span
          ( span-span-diagram 𝒮)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram 𝒯)
    hom-span-equiv-span-diagram =
      hom-equiv-span
        ( concat-span
          ( span-span-diagram 𝒮)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram 𝒯)
        ( equiv-span-equiv-span-diagram)

    hom-equiv-span-diagram : hom-span-diagram 𝒮 𝒯
    pr1 hom-equiv-span-diagram = map-domain-equiv-span-diagram
    pr1 (pr2 hom-equiv-span-diagram) = map-codomain-equiv-span-diagram
    pr2 (pr2 hom-equiv-span-diagram) = hom-span-equiv-span-diagram

    is-equiv-equiv-span-diagram :
      is-equiv-hom-span-diagram 𝒮 𝒯 hom-equiv-span-diagram
    pr1 is-equiv-equiv-span-diagram =
      is-equiv-map-domain-equiv-span-diagram
    pr1 (pr2 is-equiv-equiv-span-diagram) =
      is-equiv-map-codomain-equiv-span-diagram
    pr2 (pr2 is-equiv-equiv-span-diagram) =
      is-equiv-spanning-map-equiv-span-diagram

    compute-equiv-span-diagram :
      Σ (hom-span-diagram 𝒮 𝒯) (is-equiv-hom-span-diagram 𝒮 𝒯) ≃
      equiv-span-diagram
    compute-equiv-span-diagram =
      ( equiv-tot
        ( λ e →
          ( equiv-tot
            ( λ f →
              compute-equiv-span
                ( concat-span
                  ( span-span-diagram 𝒮)
                  ( map-equiv e)
                  ( map-equiv f))
                ( span-span-diagram 𝒯))) ∘e
          ( interchange-Σ-Σ _))) ∘e
      ( interchange-Σ-Σ _)
```

### The identity equivalence of span diagrams

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  id-equiv-span-diagram : equiv-span-diagram 𝒮 𝒮
  pr1 id-equiv-span-diagram = id-equiv
  pr1 (pr2 id-equiv-span-diagram) = id-equiv
  pr2 (pr2 id-equiv-span-diagram) = id-equiv-span (span-span-diagram 𝒮)
```

## Properties

### Extensionality of span diagrams

Equality of span diagrams is equivalent to equivalences of span diagrams.

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  equiv-eq-span-diagram :
    (𝒯 : span-diagram l1 l2 l3) → 𝒮 ＝ 𝒯 → equiv-span-diagram 𝒮 𝒯
  equiv-eq-span-diagram 𝒯 refl = id-equiv-span-diagram 𝒮

  abstract
    is-torsorial-equiv-span-diagram :
      is-torsorial (equiv-span-diagram {l1} {l2} {l3} {l1} {l2} {l3} 𝒮)
    is-torsorial-equiv-span-diagram =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv (domain-span-diagram 𝒮))
        ( domain-span-diagram 𝒮 , id-equiv)
        ( is-torsorial-Eq-structure
          ( is-torsorial-equiv (codomain-span-diagram 𝒮))
          ( codomain-span-diagram 𝒮 , id-equiv)
          ( is-torsorial-equiv-span (span-span-diagram 𝒮)))

  abstract
    is-equiv-equiv-eq-span-diagram :
      (𝒯 : span-diagram l1 l2 l3) → is-equiv (equiv-eq-span-diagram 𝒯)
    is-equiv-equiv-eq-span-diagram =
      fundamental-theorem-id
        ( is-torsorial-equiv-span-diagram)
        ( equiv-eq-span-diagram)

  extensionality-span-diagram :
    (𝒯 : span-diagram l1 l2 l3) → (𝒮 ＝ 𝒯) ≃ equiv-span-diagram 𝒮 𝒯
  pr1 (extensionality-span-diagram 𝒯) = equiv-eq-span-diagram 𝒯
  pr2 (extensionality-span-diagram 𝒯) = is-equiv-equiv-eq-span-diagram 𝒯

  eq-equiv-span-diagram :
    (𝒯 : span-diagram l1 l2 l3) → equiv-span-diagram 𝒮 𝒯 → 𝒮 ＝ 𝒯
  eq-equiv-span-diagram 𝒯 = map-inv-equiv (extensionality-span-diagram 𝒯)
```
