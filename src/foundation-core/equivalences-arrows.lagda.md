# Equivalences of arrows

```agda
module foundation-core.equivalences-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
```

</details>

## Idea

An {{#concept "equivalence of arrows" Agda=equiv-arrow}} from a function
`f : A → B` to a function `g : X → Y` is a
[morphism of arrows](foundation.morphisms-arrows.md)

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

## Definitions

### The predicate of being an equivalence of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  is-equiv-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-hom-arrow =
    ( is-equiv (map-domain-hom-arrow f g h)) ×
    ( is-equiv (map-codomain-hom-arrow f g h))

  is-equiv-map-domain-is-equiv-hom-arrow :
    is-equiv-hom-arrow → is-equiv (map-domain-hom-arrow f g h)
  is-equiv-map-domain-is-equiv-hom-arrow = pr1

  is-equiv-map-codomain-is-equiv-hom-arrow :
    is-equiv-hom-arrow → is-equiv (map-codomain-hom-arrow f g h)
  is-equiv-map-codomain-is-equiv-hom-arrow = pr2
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
  equiv-arrow = Σ (A ≃ X) (λ i → Σ (B ≃ Y) (coherence-equiv-arrow i))

  module _
    (e : equiv-arrow)
    where

    equiv-domain-equiv-arrow : A ≃ X
    equiv-domain-equiv-arrow = pr1 e

    map-domain-equiv-arrow : A → X
    map-domain-equiv-arrow = map-equiv equiv-domain-equiv-arrow

    map-inv-domain-equiv-arrow : X → A
    map-inv-domain-equiv-arrow = map-inv-equiv equiv-domain-equiv-arrow

    is-equiv-map-domain-equiv-arrow : is-equiv map-domain-equiv-arrow
    is-equiv-map-domain-equiv-arrow =
      is-equiv-map-equiv equiv-domain-equiv-arrow

    equiv-codomain-equiv-arrow : B ≃ Y
    equiv-codomain-equiv-arrow = pr1 (pr2 e)

    map-codomain-equiv-arrow : B → Y
    map-codomain-equiv-arrow = map-equiv equiv-codomain-equiv-arrow

    map-inv-codomain-equiv-arrow : Y → B
    map-inv-codomain-equiv-arrow = map-inv-equiv equiv-codomain-equiv-arrow

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

### The identity equivalence of arrows

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  id-equiv-arrow : equiv-arrow f f
  pr1 id-equiv-arrow = id-equiv
  pr1 (pr2 id-equiv-arrow) = id-equiv
  pr2 (pr2 id-equiv-arrow) = refl-htpy
```

### Composition of equivalences of arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V)
  (b : equiv-arrow g h) (a : equiv-arrow f g)
  where

  equiv-domain-comp-equiv-arrow : A ≃ U
  equiv-domain-comp-equiv-arrow =
    equiv-domain-equiv-arrow g h b ∘e equiv-domain-equiv-arrow f g a

  map-domain-comp-equiv-arrow : A → U
  map-domain-comp-equiv-arrow = map-equiv equiv-domain-comp-equiv-arrow

  equiv-codomain-comp-equiv-arrow : B ≃ V
  equiv-codomain-comp-equiv-arrow =
    equiv-codomain-equiv-arrow g h b ∘e equiv-codomain-equiv-arrow f g a

  map-codomain-comp-equiv-arrow : B → V
  map-codomain-comp-equiv-arrow = map-equiv equiv-codomain-comp-equiv-arrow

  coh-comp-equiv-arrow :
    coherence-equiv-arrow f h
      ( equiv-domain-comp-equiv-arrow)
      ( equiv-codomain-comp-equiv-arrow)
  coh-comp-equiv-arrow =
    coh-comp-hom-arrow f g h
      ( hom-equiv-arrow g h b)
      ( hom-equiv-arrow f g a)

  comp-equiv-arrow : equiv-arrow f h
  pr1 comp-equiv-arrow = equiv-domain-comp-equiv-arrow
  pr1 (pr2 comp-equiv-arrow) = equiv-codomain-comp-equiv-arrow
  pr2 (pr2 comp-equiv-arrow) = coh-comp-equiv-arrow

  hom-comp-equiv-arrow : hom-arrow f h
  hom-comp-equiv-arrow = hom-equiv-arrow f h comp-equiv-arrow
```

### Inverses of equivalences of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : equiv-arrow f g)
  where

  equiv-domain-inv-equiv-arrow : X ≃ A
  equiv-domain-inv-equiv-arrow = inv-equiv (equiv-domain-equiv-arrow f g α)

  map-domain-inv-equiv-arrow : X → A
  map-domain-inv-equiv-arrow = map-equiv equiv-domain-inv-equiv-arrow

  equiv-codomain-inv-equiv-arrow : Y ≃ B
  equiv-codomain-inv-equiv-arrow = inv-equiv (equiv-codomain-equiv-arrow f g α)

  map-codomain-inv-equiv-arrow : Y → B
  map-codomain-inv-equiv-arrow = map-equiv equiv-codomain-inv-equiv-arrow

  coh-inv-equiv-arrow :
    coherence-equiv-arrow g f
      ( equiv-domain-inv-equiv-arrow)
      ( equiv-codomain-inv-equiv-arrow)
  coh-inv-equiv-arrow =
    horizontal-inv-equiv-coherence-square-maps
      ( equiv-domain-equiv-arrow f g α)
      ( f)
      ( g)
      ( equiv-codomain-equiv-arrow f g α)
      ( coh-equiv-arrow f g α)

  inv-equiv-arrow : equiv-arrow g f
  pr1 inv-equiv-arrow = equiv-domain-inv-equiv-arrow
  pr1 (pr2 inv-equiv-arrow) = equiv-codomain-inv-equiv-arrow
  pr2 (pr2 inv-equiv-arrow) = coh-inv-equiv-arrow

  hom-inv-equiv-arrow : hom-arrow g f
  hom-inv-equiv-arrow = hom-equiv-arrow g f inv-equiv-arrow

  is-equiv-inv-equiv-arrow : is-equiv-hom-arrow g f hom-inv-equiv-arrow
  is-equiv-inv-equiv-arrow = is-equiv-equiv-arrow g f inv-equiv-arrow
```

### If a map is equivalent to an equivalence, then it is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : equiv-arrow f g)
  where

  is-equiv-source-is-equiv-target-equiv-arrow : is-equiv g → is-equiv f
  is-equiv-source-is-equiv-target-equiv-arrow =
    is-equiv-left-is-equiv-right-square
      ( f)
      ( g)
      ( map-domain-equiv-arrow f g α)
      ( map-codomain-equiv-arrow f g α)
      ( coh-equiv-arrow f g α)
      ( is-equiv-map-domain-equiv-arrow f g α)
      ( is-equiv-map-codomain-equiv-arrow f g α)

  is-equiv-target-is-equiv-source-equiv-arrow : is-equiv f → is-equiv g
  is-equiv-target-is-equiv-source-equiv-arrow =
    is-equiv-right-is-equiv-left-square
      ( f)
      ( g)
      ( map-domain-equiv-arrow f g α)
      ( map-codomain-equiv-arrow f g α)
      ( coh-equiv-arrow f g α)
      ( is-equiv-map-domain-equiv-arrow f g α)
      ( is-equiv-map-codomain-equiv-arrow f g α)
```
