# Equivalences of arrows

```agda
module foundation.equivalences-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.morphisms-arrows
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.propositions
```

</details>

## Idea

An {{#concept "equivalence of arrows"}} is a
[morphism of arrows](foundation.morphisms-arrows.md)

```text
        i
    A -----> X
    |   ≃    |
  f |        | g
    V   ≃    V
    B -----> Y
        j
```

in which the top and bottom morphisms are
[equivalences](foundation-core.equivalences.md).

## Definitions

### The predicate of being an equivalence of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  is-equiv-prop-hom-arrow : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-prop-hom-arrow =
    prod-Prop
      ( is-equiv-Prop (map-domain-hom-arrow f g h))
      ( is-equiv-Prop (map-codomain-hom-arrow f g h))

  is-equiv-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-hom-arrow =
    type-Prop is-equiv-prop-hom-arrow

  is-prop-is-equiv-hom-arrow : is-prop is-equiv-hom-arrow
  is-prop-is-equiv-hom-arrow = is-prop-type-Prop is-equiv-prop-hom-arrow
```

### Equivalences of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  coherence-equiv-arrow : (A ≃ X) → (B ≃ Y) → UU (l1 ⊔ l4)
  coherence-equiv-arrow i j =
    coherence-hom-arrow f g (map-equiv i) (map-equiv j)

  equiv-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-arrow =
    Σ (A ≃ X) (λ i → Σ (B ≃ Y) (coherence-equiv-arrow i))

  module _
    (e : equiv-arrow)
    where

    equiv-domain-equiv-arrow : A ≃ X
    equiv-domain-equiv-arrow = pr1 e

    map-domain-equiv-arrow : A → X
    map-domain-equiv-arrow = map-equiv equiv-domain-equiv-arrow

    is-equiv-map-domain-equiv-arrow : is-equiv map-domain-equiv-arrow
    is-equiv-map-domain-equiv-arrow =
      is-equiv-map-equiv equiv-domain-equiv-arrow

    equiv-codomain-equiv-arrow : B ≃ Y
    equiv-codomain-equiv-arrow = pr1 (pr2 e)

    map-codomain-equiv-arrow : B → Y
    map-codomain-equiv-arrow = map-equiv equiv-codomain-equiv-arrow

    is-equiv-map-codomain-equiv-arrow : is-equiv map-codomain-equiv-arrow
    is-equiv-map-codomain-equiv-arrow =
      is-equiv-map-equiv equiv-codomain-equiv-arrow

    coh-equiv-arrow :
      coherence-equiv-arrow
        ( equiv-domain-equiv-arrow)
        ( equiv-codomain-equiv-arrow)
    coh-equiv-arrow = pr2 (pr2 e)

    hom-equiv-arrow : hom-arrow f g
    pr1 hom-equiv-arrow = map-domain-equiv-arrow
    pr1 (pr2 hom-equiv-arrow) = map-codomain-equiv-arrow
    pr2 (pr2 hom-equiv-arrow) = coh-equiv-arrow

    is-equiv-equiv-arrow : is-equiv-hom-arrow f g hom-equiv-arrow
    pr1 is-equiv-equiv-arrow = is-equiv-map-domain-equiv-arrow
    pr2 is-equiv-equiv-arrow = is-equiv-map-codomain-equiv-arrow

    span-equiv-arrow :
      span l1 B X
    span-equiv-arrow =
      span-hom-arrow f g hom-equiv-arrow

    span-diagram-equiv-arrow : span-diagram l2 l3 l1
    pr1 span-diagram-equiv-arrow = B
    pr1 (pr2 span-diagram-equiv-arrow) = X
    pr2 (pr2 span-diagram-equiv-arrow) = span-equiv-arrow
```
