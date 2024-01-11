# Equivalences of span diagrams

```agda
module foundation.equivalences-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.equivalences-spans
open import foundation.extensions-spans
open import foundation.fundamental-theorem-of-identity-types
open import foundation.morphisms-span-diagrams
open import foundation.morphisms-spans
open import foundation.propositions
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An {{#concept "equivalence of span diagrams"}} from a
[span diagram](foundation.span-diagrams.md) `A <-f- S -g-> B`
to a span diagram `C <-h- T -k-> D` consists of
[equivalences](foundation-core.equivalences.md) `u : A ≃ C`, `v : B ≃ D`,
and `w : S ≃ T` [equipped](foundation.structure.md) with two
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

## Definitions

### The predicate of being an equivalence of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (s : span-diagram l1 l2 l3) (t : span-diagram l4 l5 l6)
  (f : hom-span-diagram s t)
  where

  is-equiv-prop-hom-span-diagram : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-equiv-prop-hom-span-diagram =
    prod-Prop
      ( is-equiv-Prop (map-domain-hom-span-diagram s t f))
      ( prod-Prop
        ( is-equiv-Prop (map-codomain-hom-span-diagram s t f))
        ( is-equiv-Prop (spanning-map-hom-span-diagram s t f)))

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
  (s : span-diagram l1 l2 l3) (t : span-diagram l4 l5 l6)
  where

  equiv-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  equiv-span-diagram =
    Σ ( domain-span-diagram s ≃ domain-span-diagram t)
      ( λ e →
        Σ ( codomain-span-diagram s ≃ codomain-span-diagram t)
          ( λ f →
            equiv-span
              ( extend-span (span-span-diagram s) (map-equiv e) (map-equiv f))
              ( span-span-diagram t)))

  module _
    (e : equiv-span-diagram)
    where

    equiv-domain-equiv-span-diagram :
      domain-span-diagram s ≃ domain-span-diagram t
    equiv-domain-equiv-span-diagram = pr1 e

    map-domain-equiv-span-diagram :
      domain-span-diagram s → domain-span-diagram t
    map-domain-equiv-span-diagram = map-equiv equiv-domain-equiv-span-diagram

    is-equiv-map-domain-equiv-span-diagram :
      is-equiv map-domain-equiv-span-diagram
    is-equiv-map-domain-equiv-span-diagram =
      is-equiv-map-equiv equiv-domain-equiv-span-diagram

    equiv-codomain-equiv-span-diagram :
      codomain-span-diagram s ≃ codomain-span-diagram t
    equiv-codomain-equiv-span-diagram = pr1 (pr2 e)

    map-codomain-equiv-span-diagram :
      codomain-span-diagram s → codomain-span-diagram t
    map-codomain-equiv-span-diagram =
      map-equiv equiv-codomain-equiv-span-diagram

    is-equiv-map-codomain-equiv-span-diagram :
      is-equiv map-codomain-equiv-span-diagram
    is-equiv-map-codomain-equiv-span-diagram =
      is-equiv-map-equiv equiv-codomain-equiv-span-diagram

    equiv-span-equiv-span-diagram :
      equiv-span
        ( extend-span
          ( span-span-diagram s)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram t)
    equiv-span-equiv-span-diagram =
      pr2 (pr2 e)

    spanning-equiv-equiv-span-diagram :
      spanning-type-span-diagram s ≃ spanning-type-span-diagram t
    spanning-equiv-equiv-span-diagram =
      equiv-equiv-span
        ( extend-span
          ( span-span-diagram s)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram t)
        ( equiv-span-equiv-span-diagram)

    spanning-map-equiv-span-diagram :
      spanning-type-span-diagram s → spanning-type-span-diagram t
    spanning-map-equiv-span-diagram =
      map-equiv-span
        ( extend-span
          ( span-span-diagram s)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram t)
        ( equiv-span-equiv-span-diagram)

    is-equiv-spanning-map-equiv-span-diagram :
      is-equiv spanning-map-equiv-span-diagram
    is-equiv-spanning-map-equiv-span-diagram =
      is-equiv-equiv-span
        ( extend-span
          ( span-span-diagram s)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram t)
        ( equiv-span-equiv-span-diagram)

    left-square-equiv-span-diagram :
      coherence-square-maps
        ( spanning-map-equiv-span-diagram)
        ( left-map-span-diagram s)
        ( left-map-span-diagram t)
        ( map-domain-equiv-span-diagram)
    left-square-equiv-span-diagram =
      left-triangle-equiv-span
        ( extend-span
          ( span-span-diagram s)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram t)
        ( equiv-span-equiv-span-diagram)

    equiv-left-arrow-equiv-span-diagram :
      equiv-arrow (left-map-span-diagram s) (left-map-span-diagram t)
    pr1 equiv-left-arrow-equiv-span-diagram =
      spanning-equiv-equiv-span-diagram
    pr1 (pr2 equiv-left-arrow-equiv-span-diagram) =
      equiv-domain-equiv-span-diagram
    pr2 (pr2 equiv-left-arrow-equiv-span-diagram) =
      left-square-equiv-span-diagram

    right-square-equiv-span-diagram :
      coherence-square-maps
        ( spanning-map-equiv-span-diagram)
        ( right-map-span-diagram s)
        ( right-map-span-diagram t)
        ( map-codomain-equiv-span-diagram)
    right-square-equiv-span-diagram =
      right-triangle-equiv-span
        ( extend-span
          ( span-span-diagram s)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram t)
        ( equiv-span-equiv-span-diagram)

    equiv-right-arrow-equiv-span-diagram :
      equiv-arrow (right-map-span-diagram s) (right-map-span-diagram t)
    pr1 equiv-right-arrow-equiv-span-diagram =
      spanning-equiv-equiv-span-diagram
    pr1 (pr2 equiv-right-arrow-equiv-span-diagram) =
      equiv-codomain-equiv-span-diagram
    pr2 (pr2 equiv-right-arrow-equiv-span-diagram) =
      right-square-equiv-span-diagram

    hom-span-equiv-span-diagram :
      hom-span
        ( extend-span
          ( span-span-diagram s)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram t)
    hom-span-equiv-span-diagram =
      hom-equiv-span
        ( extend-span
          ( span-span-diagram s)
          ( map-domain-equiv-span-diagram)
          ( map-codomain-equiv-span-diagram))
        ( span-span-diagram t)
        ( equiv-span-equiv-span-diagram)

    hom-equiv-span-diagram : hom-span-diagram s t
    pr1 hom-equiv-span-diagram = map-domain-equiv-span-diagram
    pr1 (pr2 hom-equiv-span-diagram) = map-codomain-equiv-span-diagram
    pr2 (pr2 hom-equiv-span-diagram) = hom-span-equiv-span-diagram

    is-equiv-equiv-span-diagram :
      is-equiv-hom-span-diagram s t hom-equiv-span-diagram
    pr1 is-equiv-equiv-span-diagram =
      is-equiv-map-domain-equiv-span-diagram
    pr1 (pr2 is-equiv-equiv-span-diagram) =
      is-equiv-map-codomain-equiv-span-diagram
    pr2 (pr2 is-equiv-equiv-span-diagram) =
      is-equiv-spanning-map-equiv-span-diagram

    compute-equiv-span-diagram :
      Σ (hom-span-diagram s t) (is-equiv-hom-span-diagram s t) ≃
      equiv-span-diagram
    compute-equiv-span-diagram =
      ( equiv-tot
        ( λ e →
          ( equiv-tot
            ( λ f →
              compute-equiv-span
                ( extend-span
                  ( span-span-diagram s)
                  ( map-equiv e)
                  ( map-equiv f))
                ( span-span-diagram t))) ∘e
          ( interchange-Σ-Σ _))) ∘e
      ( interchange-Σ-Σ _)
```

### The identity equivalence of span diagrams

```agda
module _
  {l1 l2 l3 : Level} (s : span-diagram l1 l2 l3)
  where

  id-equiv-span-diagram : equiv-span-diagram s s
  pr1 id-equiv-span-diagram = id-equiv
  pr1 (pr2 id-equiv-span-diagram) = id-equiv
  pr2 (pr2 id-equiv-span-diagram) = id-equiv-span (span-span-diagram s)
```

## Properties

### Extensionality of span diagrams

Equality of span diagrams is equivalent to equivalences of span diagrams

```agda
module _
  {l1 l2 l3 : Level} (s : span-diagram l1 l2 l3)
  where

  equiv-eq-span-diagram :
    (t : span-diagram l1 l2 l3) → (s ＝ t) → equiv-span-diagram s t
  equiv-eq-span-diagram t refl = id-equiv-span-diagram s

  is-torsorial-equiv-span-diagram :
    is-torsorial (equiv-span-diagram {l1} {l2} {l3} {l1} {l2} {l3} s)
  is-torsorial-equiv-span-diagram =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (domain-span-diagram s))
      ( domain-span-diagram s , id-equiv)
      ( is-torsorial-Eq-structure
        ( is-torsorial-equiv (codomain-span-diagram s))
        ( codomain-span-diagram s , id-equiv)
        ( is-torsorial-equiv-span (span-span-diagram s)))

  is-equiv-equiv-eq-span-diagram :
    (t : span-diagram l1 l2 l3) → is-equiv (equiv-eq-span-diagram t)
  is-equiv-equiv-eq-span-diagram =
    fundamental-theorem-id is-torsorial-equiv-span-diagram equiv-eq-span-diagram

  extensionality-span-diagram :
    (t : span-diagram l1 l2 l3) → (s ＝ t) ≃ equiv-span-diagram s t
  pr1 (extensionality-span-diagram t) = equiv-eq-span-diagram t
  pr2 (extensionality-span-diagram t) = is-equiv-equiv-eq-span-diagram t

  eq-equiv-span-diagram :
    (t : span-diagram l1 l2 l3) → equiv-span-diagram s t → s ＝ t
  eq-equiv-span-diagram t = map-inv-equiv (extensionality-span-diagram t)
```
