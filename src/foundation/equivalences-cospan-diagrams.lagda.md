# Equivalences of cospan diagrams

```agda
module foundation.equivalences-cospan-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.equivalences-cospans
open import foundation.fundamental-theorem-of-identity-types
open import foundation.morphisms-cospan-diagrams
open import foundation.morphisms-cospans
open import foundation.operations-cospans
open import foundation.propositions
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

An {{#concept "equivalence of cospan diagrams" Agda=equiv-cospan-diagram}} from
a [cospan diagram](foundation.cospan-diagrams.md) `A -f-> S <-g- B` to a cospan
diagram `C -h-> T <-k- D` consists of
[equivalences](foundation-core.equivalences.md) `u : A ≃ C`, `v : B ≃ D`, and
`w : S ≃ T` [equipped](foundation.structure.md) with two
[homotopies](foundation-core.homotopies.md) witnessing that the diagram

```text
         f         g
    A ------> S <------ B
    |         |         |
  u |         | w       | v
    ∨         ∨         ∨
    C ------> T <------ D
         h         k
```

[commutes](foundation-core.commuting-squares-of-maps.md).

## Definitions

### The predicate of being an equivalence of cospan diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒮 : cospan-diagram l1 l2 l3) (𝒯 : cospan-diagram l4 l5 l6)
  (f : hom-cospan-diagram 𝒮 𝒯)
  where

  is-equiv-prop-hom-cospan-diagram : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-equiv-prop-hom-cospan-diagram =
    product-Prop
      ( is-equiv-Prop (map-domain-hom-cospan-diagram 𝒮 𝒯 f))
      ( product-Prop
        ( is-equiv-Prop (map-codomain-hom-cospan-diagram 𝒮 𝒯 f))
        ( is-equiv-Prop (cospanning-map-hom-cospan-diagram 𝒮 𝒯 f)))

  is-equiv-hom-cospan-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-equiv-hom-cospan-diagram = type-Prop is-equiv-prop-hom-cospan-diagram

  is-prop-is-equiv-hom-cospan-diagram : is-prop is-equiv-hom-cospan-diagram
  is-prop-is-equiv-hom-cospan-diagram =
    is-prop-type-Prop is-equiv-prop-hom-cospan-diagram
```

### Equivalences of cospan diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒮 : cospan-diagram l1 l2 l3) (𝒯 : cospan-diagram l4 l5 l6)
  where

  equiv-cospan-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  equiv-cospan-diagram =
    Σ ( domain-cospan-diagram 𝒮 ≃ domain-cospan-diagram 𝒯)
      ( λ e →
        Σ ( codomain-cospan-diagram 𝒮 ≃ codomain-cospan-diagram 𝒯)
          ( λ f →
            equiv-cospan
              ( cospan-cospan-diagram 𝒮)
              ( concat-cospan
                ( cospan-cospan-diagram 𝒯)
                ( map-equiv e)
                ( map-equiv f))))

  module _
    (e : equiv-cospan-diagram)
    where

    equiv-domain-equiv-cospan-diagram :
      domain-cospan-diagram 𝒮 ≃ domain-cospan-diagram 𝒯
    equiv-domain-equiv-cospan-diagram = pr1 e

    map-domain-equiv-cospan-diagram :
      domain-cospan-diagram 𝒮 → domain-cospan-diagram 𝒯
    map-domain-equiv-cospan-diagram =
      map-equiv equiv-domain-equiv-cospan-diagram

    is-equiv-map-domain-equiv-cospan-diagram :
      is-equiv map-domain-equiv-cospan-diagram
    is-equiv-map-domain-equiv-cospan-diagram =
      is-equiv-map-equiv equiv-domain-equiv-cospan-diagram

    equiv-codomain-equiv-cospan-diagram :
      codomain-cospan-diagram 𝒮 ≃ codomain-cospan-diagram 𝒯
    equiv-codomain-equiv-cospan-diagram = pr1 (pr2 e)

    map-codomain-equiv-cospan-diagram :
      codomain-cospan-diagram 𝒮 → codomain-cospan-diagram 𝒯
    map-codomain-equiv-cospan-diagram =
      map-equiv equiv-codomain-equiv-cospan-diagram

    is-equiv-map-codomain-equiv-cospan-diagram :
      is-equiv map-codomain-equiv-cospan-diagram
    is-equiv-map-codomain-equiv-cospan-diagram =
      is-equiv-map-equiv equiv-codomain-equiv-cospan-diagram

    equiv-cospan-equiv-cospan-diagram :
      equiv-cospan
        ( cospan-cospan-diagram 𝒮)
        ( concat-cospan
          ( cospan-cospan-diagram 𝒯)
          ( map-domain-equiv-cospan-diagram)
          ( map-codomain-equiv-cospan-diagram))
    equiv-cospan-equiv-cospan-diagram =
      pr2 (pr2 e)

    cospanning-equiv-equiv-cospan-diagram :
      cospanning-type-cospan-diagram 𝒮 ≃ cospanning-type-cospan-diagram 𝒯
    cospanning-equiv-equiv-cospan-diagram =
      equiv-equiv-cospan
        ( cospan-cospan-diagram 𝒮)
        ( concat-cospan
          ( cospan-cospan-diagram 𝒯)
          ( map-domain-equiv-cospan-diagram)
          ( map-codomain-equiv-cospan-diagram))
        ( equiv-cospan-equiv-cospan-diagram)

    cospanning-map-equiv-cospan-diagram :
      cospanning-type-cospan-diagram 𝒮 → cospanning-type-cospan-diagram 𝒯
    cospanning-map-equiv-cospan-diagram =
      map-equiv-cospan
        ( cospan-cospan-diagram 𝒮)
        ( concat-cospan
          ( cospan-cospan-diagram 𝒯)
          ( map-domain-equiv-cospan-diagram)
          ( map-codomain-equiv-cospan-diagram))
        ( equiv-cospan-equiv-cospan-diagram)

    is-equiv-cospanning-map-equiv-cospan-diagram :
      is-equiv cospanning-map-equiv-cospan-diagram
    is-equiv-cospanning-map-equiv-cospan-diagram =
      is-equiv-equiv-cospan
        ( cospan-cospan-diagram 𝒮)
        ( concat-cospan
          ( cospan-cospan-diagram 𝒯)
          ( map-domain-equiv-cospan-diagram)
          ( map-codomain-equiv-cospan-diagram))
        ( equiv-cospan-equiv-cospan-diagram)

    -- left-square-equiv-cospan-diagram :
    --   coherence-square-maps
    --     ( cospanning-map-equiv-cospan-diagram)
    --     ( left-map-cospan-diagram 𝒮)
    --     ( left-map-cospan-diagram 𝒯)
    --     ( map-domain-equiv-cospan-diagram)
    -- left-square-equiv-cospan-diagram =
    --   left-triangle-equiv-cospan
    --     ( concat-cospan
    --       ( cospan-cospan-diagram 𝒮)
    --       ( map-domain-equiv-cospan-diagram)
    --       ( map-codomain-equiv-cospan-diagram))
    --     ( cospan-cospan-diagram 𝒯)
    --     ( equiv-cospan-equiv-cospan-diagram)

    -- equiv-left-arrow-equiv-cospan-diagram :
    --   equiv-arrow (left-map-cospan-diagram 𝒮) (left-map-cospan-diagram 𝒯)
    -- pr1 equiv-left-arrow-equiv-cospan-diagram =
    --   cospanning-equiv-equiv-cospan-diagram
    -- pr1 (pr2 equiv-left-arrow-equiv-cospan-diagram) =
    --   equiv-domain-equiv-cospan-diagram
    -- pr2 (pr2 equiv-left-arrow-equiv-cospan-diagram) =
    --   left-square-equiv-cospan-diagram

    -- right-square-equiv-cospan-diagram :
    --   coherence-square-maps
    --     ( cospanning-map-equiv-cospan-diagram)
    --     ( right-map-cospan-diagram 𝒮)
    --     ( right-map-cospan-diagram 𝒯)
    --     ( map-codomain-equiv-cospan-diagram)
    -- right-square-equiv-cospan-diagram =
    --   right-triangle-equiv-cospan
    --     ( concat-cospan
    --       ( cospan-cospan-diagram 𝒮)
    --       ( map-domain-equiv-cospan-diagram)
    --       ( map-codomain-equiv-cospan-diagram))
    --     ( cospan-cospan-diagram 𝒯)
    --     ( equiv-cospan-equiv-cospan-diagram)

    -- equiv-right-arrow-equiv-cospan-diagram :
    --   equiv-arrow (right-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒯)
    -- pr1 equiv-right-arrow-equiv-cospan-diagram =
    --   cospanning-equiv-equiv-cospan-diagram
    -- pr1 (pr2 equiv-right-arrow-equiv-cospan-diagram) =
    --   equiv-codomain-equiv-cospan-diagram
    -- pr2 (pr2 equiv-right-arrow-equiv-cospan-diagram) =
    --   right-square-equiv-cospan-diagram

    -- hom-cospan-equiv-cospan-diagram :
    --   hom-cospan
    --     ( concat-cospan
    --       ( cospan-cospan-diagram 𝒮)
    --       ( map-domain-equiv-cospan-diagram)
    --       ( map-codomain-equiv-cospan-diagram))
    --     ( cospan-cospan-diagram 𝒯)
    -- hom-cospan-equiv-cospan-diagram =
    --   hom-equiv-cospan
    --     ( concat-cospan
    --       ( cospan-cospan-diagram 𝒮)
    --       ( map-domain-equiv-cospan-diagram)
    --       ( map-codomain-equiv-cospan-diagram))
    --     ( cospan-cospan-diagram 𝒯)
    --     ( equiv-cospan-equiv-cospan-diagram)

    -- hom-equiv-cospan-diagram : hom-cospan-diagram 𝒮 𝒯
    -- pr1 hom-equiv-cospan-diagram = map-domain-equiv-cospan-diagram
    -- pr1 (pr2 hom-equiv-cospan-diagram) = map-codomain-equiv-cospan-diagram
    -- pr2 (pr2 hom-equiv-cospan-diagram) = hom-cospan-equiv-cospan-diagram

    -- is-equiv-equiv-cospan-diagram :
    --   is-equiv-hom-cospan-diagram 𝒮 𝒯 hom-equiv-cospan-diagram
    -- pr1 is-equiv-equiv-cospan-diagram =
    --   is-equiv-map-domain-equiv-cospan-diagram
    -- pr1 (pr2 is-equiv-equiv-cospan-diagram) =
    --   is-equiv-map-codomain-equiv-cospan-diagram
    -- pr2 (pr2 is-equiv-equiv-cospan-diagram) =
    --   is-equiv-cospanning-map-equiv-cospan-diagram

    -- compute-equiv-cospan-diagram :
    --   Σ (hom-cospan-diagram 𝒮 𝒯) (is-equiv-hom-cospan-diagram 𝒮 𝒯) ≃
    --   equiv-cospan-diagram
    -- compute-equiv-cospan-diagram =
    --   ( equiv-tot
    --     ( λ e →
    --       ( equiv-tot
    --         ( λ f →
    --           compute-equiv-cospan
    --             ( concat-cospan
    --               ( cospan-cospan-diagram 𝒮)
    --               ( map-equiv e)
    --               ( map-equiv f))
    --             ( cospan-cospan-diagram 𝒯))) ∘e
    --       ( interchange-Σ-Σ _))) ∘e
    --   ( interchange-Σ-Σ _)
```

### The identity equivalence of cospan diagrams

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : cospan-diagram l1 l2 l3)
  where

  id-equiv-cospan-diagram : equiv-cospan-diagram 𝒮 𝒮
  pr1 id-equiv-cospan-diagram = id-equiv
  pr1 (pr2 id-equiv-cospan-diagram) = id-equiv
  pr2 (pr2 id-equiv-cospan-diagram) = id-equiv-cospan (cospan-cospan-diagram 𝒮)
```

## Properties

### Extensionality of cospan diagrams

Equality of cospan diagrams is equivalent to equivalences of cospan diagrams.

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : cospan-diagram l1 l2 l3)
  where

  equiv-eq-cospan-diagram :
    (𝒯 : cospan-diagram l1 l2 l3) → 𝒮 ＝ 𝒯 → equiv-cospan-diagram 𝒮 𝒯
  equiv-eq-cospan-diagram 𝒯 refl = id-equiv-cospan-diagram 𝒮

  abstract
    is-torsorial-equiv-cospan-diagram :
      is-torsorial (equiv-cospan-diagram {l1} {l2} {l3} {l1} {l2} {l3} 𝒮)
    is-torsorial-equiv-cospan-diagram =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv (domain-cospan-diagram 𝒮))
        ( domain-cospan-diagram 𝒮 , id-equiv)
        ( is-torsorial-Eq-structure
          ( is-torsorial-equiv (codomain-cospan-diagram 𝒮))
          ( codomain-cospan-diagram 𝒮 , id-equiv)
          ( is-torsorial-equiv-cospan (cospan-cospan-diagram 𝒮)))

  abstract
    is-equiv-equiv-eq-cospan-diagram :
      (𝒯 : cospan-diagram l1 l2 l3) → is-equiv (equiv-eq-cospan-diagram 𝒯)
    is-equiv-equiv-eq-cospan-diagram =
      fundamental-theorem-id
        ( is-torsorial-equiv-cospan-diagram)
        ( equiv-eq-cospan-diagram)

  extensionality-cospan-diagram :
    (𝒯 : cospan-diagram l1 l2 l3) → (𝒮 ＝ 𝒯) ≃ equiv-cospan-diagram 𝒮 𝒯
  pr1 (extensionality-cospan-diagram 𝒯) = equiv-eq-cospan-diagram 𝒯
  pr2 (extensionality-cospan-diagram 𝒯) = is-equiv-equiv-eq-cospan-diagram 𝒯

  eq-equiv-cospan-diagram :
    (𝒯 : cospan-diagram l1 l2 l3) → equiv-cospan-diagram 𝒮 𝒯 → 𝒮 ＝ 𝒯
  eq-equiv-cospan-diagram 𝒯 = map-inv-equiv (extensionality-cospan-diagram 𝒯)
```
