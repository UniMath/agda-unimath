# Equivalences of arrows

```agda
module foundation.equivalences-arrows where

open import foundation-core.equivalences-arrows public
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-arrows
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.retractions
open import foundation.retracts-of-arrows
open import foundation.sections
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

An **equivalence of arrows** from a function `f : A → B` to a function
`g : X → Y` is a [morphism of arrows](foundation.morphisms-arrows.md)

```text
         i
    A ------> X
    |         |
  f |         | g
    ∨         ∨
    B ------> Y
         j
```

in which `i` and `j` are [equivalences](foundation-core.equivalences.md).

## Properties

### Being an equivalence of arrows is a proposition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  is-equiv-prop-hom-arrow : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-prop-hom-arrow =
    product-Prop
      ( is-equiv-Prop (map-domain-hom-arrow f g h))
      ( is-equiv-Prop (map-codomain-hom-arrow f g h))

  is-prop-is-equiv-hom-arrow : is-prop (is-equiv-hom-arrow f g h)
  is-prop-is-equiv-hom-arrow = is-prop-type-Prop is-equiv-prop-hom-arrow
```

### If a map is equivalent to an embedding, then it is an embedding

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : equiv-arrow f g)
  where

  is-emb-source-is-emb-target-equiv-arrow : is-emb g → is-emb f
  is-emb-source-is-emb-target-equiv-arrow =
    is-emb-top-is-emb-bottom-is-equiv-coherence-square-maps
      ( f)
      ( map-domain-equiv-arrow f g α)
      ( map-codomain-equiv-arrow f g α)
      ( g)
      ( inv-htpy (coh-equiv-arrow f g α))
      ( is-equiv-map-domain-equiv-arrow f g α)
      ( is-equiv-map-codomain-equiv-arrow f g α)

  is-emb-target-is-emb-source-equiv-arrow : is-emb f → is-emb g
  is-emb-target-is-emb-source-equiv-arrow =
    is-emb-bottom-is-emb-top-is-equiv-coherence-square-maps
      ( f)
      ( map-domain-equiv-arrow f g α)
      ( map-codomain-equiv-arrow f g α)
      ( g)
      ( inv-htpy (coh-equiv-arrow f g α))
      ( is-equiv-map-domain-equiv-arrow f g α)
      ( is-equiv-map-codomain-equiv-arrow f g α)
```

### Equivalences of arrows are cartesian

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : equiv-arrow f g)
  where

  is-cartesian-equiv-arrow :
    is-cartesian-hom-arrow f g (hom-equiv-arrow f g α)
  is-cartesian-equiv-arrow =
    is-pullback-is-equiv-horizontal-maps
      ( map-codomain-equiv-arrow f g α)
      ( g)
      ( cone-hom-arrow f g (hom-equiv-arrow f g α))
      ( is-equiv-map-codomain-equiv-arrow f g α)
      ( is-equiv-map-domain-equiv-arrow f g α)

  cartesian-hom-equiv-arrow : cartesian-hom-arrow f g
  pr1 cartesian-hom-equiv-arrow = hom-equiv-arrow f g α
  pr2 cartesian-hom-equiv-arrow = is-cartesian-equiv-arrow
```

### Retractions are preserved by equivalences of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  reflects-retraction-equiv-arrow :
    equiv-arrow f g → retraction g → retraction f
  reflects-retraction-equiv-arrow α =
    retraction-retract-arrow-retraction' f g
      ( retract-equiv (equiv-domain-equiv-arrow f g α))
      ( map-codomain-equiv-arrow f g α)
      ( coh-equiv-arrow f g α)

  preserves-retraction-equiv-arrow :
    equiv-arrow g f → retraction g → retraction f
  preserves-retraction-equiv-arrow α =
    reflects-retraction-equiv-arrow (inv-equiv-arrow g f α)
```

### Sections are preserved by equivalences of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  preserves-section-equiv-arrow : equiv-arrow f g → section f → section g
  preserves-section-equiv-arrow α =
    section-retract-arrow-section' g f
      ( map-domain-equiv-arrow f g α)
      ( retract-inv-equiv (equiv-codomain-equiv-arrow f g α))
      ( coh-equiv-arrow f g α)

  reflects-section-equiv-arrow : equiv-arrow g f → section f → section g
  reflects-section-equiv-arrow α =
    preserves-section-equiv-arrow (inv-equiv-arrow g f α)
```
