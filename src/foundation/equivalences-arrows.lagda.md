# Equivalences of arrows

```agda
module foundation.equivalences-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-identifications
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

An {{#concept "equivalence of arrows"}} from a function `f : A → B` to a
function `g : X → Y` is a [morphism of arrows](foundation.morphisms-arrows.md)

```text
        i
    A ----> X
    |       |
  f |   H   | g
    v       v
    B ----> Y
        j
```

such that `i` and `j` are [equivalences](foundation-core.equivalences.md).

## Definitions

### The predicate of being an equivalence of arrows on morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  is-equiv-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-hom-arrow =
    is-equiv (map-domain-hom-arrow f g α) ×
    is-equiv (map-codomain-hom-arrow f g α)

  is-equiv-map-domain-is-equiv-hom-arrow :
    is-equiv-hom-arrow → is-equiv (map-domain-hom-arrow f g α)
  is-equiv-map-domain-is-equiv-hom-arrow = pr1

  is-equiv-map-codomain-is-equiv-hom-arrow :
    is-equiv-hom-arrow → is-equiv (map-codomain-hom-arrow f g α)
  is-equiv-map-codomain-is-equiv-hom-arrow = pr2
```

### The type of equivalences of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  equiv-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-arrow = Σ (hom-arrow f g) (is-equiv-hom-arrow f g)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : equiv-arrow f g)
  where

  hom-arrow-equiv-arrow : hom-arrow f g
  hom-arrow-equiv-arrow = pr1 α

  is-equiv-hom-arrow-equiv-arrow : is-equiv-hom-arrow f g hom-arrow-equiv-arrow
  is-equiv-hom-arrow-equiv-arrow = pr2 α

  map-domain-equiv-arrow : A → X
  map-domain-equiv-arrow = map-domain-hom-arrow f g hom-arrow-equiv-arrow

  is-equiv-map-domain-equiv-arrow : is-equiv map-domain-equiv-arrow
  is-equiv-map-domain-equiv-arrow =
    is-equiv-map-domain-is-equiv-hom-arrow f g
      ( hom-arrow-equiv-arrow)
      ( is-equiv-hom-arrow-equiv-arrow)

  equiv-domain-equiv-arrow : A ≃ X
  pr1 equiv-domain-equiv-arrow = map-domain-equiv-arrow
  pr2 equiv-domain-equiv-arrow = is-equiv-map-domain-equiv-arrow

  map-codomain-equiv-arrow : B → Y
  map-codomain-equiv-arrow = map-codomain-hom-arrow f g hom-arrow-equiv-arrow

  is-equiv-map-codomain-equiv-arrow : is-equiv map-codomain-equiv-arrow
  is-equiv-map-codomain-equiv-arrow =
    is-equiv-map-codomain-is-equiv-hom-arrow f g
      ( hom-arrow-equiv-arrow)
      ( is-equiv-hom-arrow-equiv-arrow)

  equiv-codomain-equiv-arrow : B ≃ Y
  pr1 equiv-codomain-equiv-arrow = map-codomain-equiv-arrow
  pr2 equiv-codomain-equiv-arrow = is-equiv-map-codomain-equiv-arrow

  coh-equiv-arrow :
    coherence-square-maps map-domain-equiv-arrow f g map-codomain-equiv-arrow
  coh-equiv-arrow = coh-hom-arrow f g hom-arrow-equiv-arrow
```

### The identity equivalence of arrows

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  id-equiv-arrow : equiv-arrow f f
  pr1 id-equiv-arrow = id-hom-arrow
  pr1 (pr2 id-equiv-arrow) = is-equiv-id
  pr2 (pr2 id-equiv-arrow) = is-equiv-id
```

### Composition of equivalences of arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V)
  (b : equiv-arrow g h) (a : equiv-arrow f g)
  where

  comp-equiv-arrow : equiv-arrow f h
  pr1 comp-equiv-arrow =
    comp-hom-arrow f g h
      ( hom-arrow-equiv-arrow g h b)
      ( hom-arrow-equiv-arrow f g a)
  pr1 (pr2 comp-equiv-arrow) =
    is-equiv-comp
      ( map-domain-equiv-arrow g h b)
      ( map-domain-equiv-arrow f g a)
      ( is-equiv-map-domain-equiv-arrow f g a)
      ( is-equiv-map-domain-equiv-arrow g h b)
  pr2 (pr2 comp-equiv-arrow) =
    is-equiv-comp
      ( map-codomain-equiv-arrow g h b)
      ( map-codomain-equiv-arrow f g a)
      ( is-equiv-map-codomain-equiv-arrow f g a)
      ( is-equiv-map-codomain-equiv-arrow g h b)
```

### Inverses of equivalences of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : equiv-arrow f g)
  where

  hom-inv-equiv-arrow : hom-arrow g f
  pr1 hom-inv-equiv-arrow =
    map-inv-is-equiv (is-equiv-map-domain-equiv-arrow f g α)
  pr1 (pr2 hom-inv-equiv-arrow) =
    map-inv-is-equiv (is-equiv-map-codomain-equiv-arrow f g α)
  pr2 (pr2 hom-inv-equiv-arrow) =
    coherence-square-inv-horizontal
      ( equiv-domain-equiv-arrow f g α)
      ( f)
      ( g)
      ( equiv-codomain-equiv-arrow f g α)
      ( coh-equiv-arrow f g α)

  is-equiv-inv-equiv-arrow : is-equiv-hom-arrow g f hom-inv-equiv-arrow
  pr1 is-equiv-inv-equiv-arrow =
    is-equiv-map-inv-is-equiv (is-equiv-map-domain-equiv-arrow f g α)
  pr2 is-equiv-inv-equiv-arrow =
    is-equiv-map-inv-is-equiv (is-equiv-map-codomain-equiv-arrow f g α)

  inv-equiv-arrow : equiv-arrow g f
  pr1 inv-equiv-arrow = hom-inv-equiv-arrow
  pr2 inv-equiv-arrow = is-equiv-inv-equiv-arrow
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

### Equivalences of arrows are cartesian

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : equiv-arrow f g)
  where

  is-cartesian-equiv-arrow :
    is-cartesian-hom-arrow f g (hom-arrow-equiv-arrow f g α)
  is-cartesian-equiv-arrow =
    is-pullback-is-equiv-horizontal-maps
      ( map-codomain-equiv-arrow f g α)
      ( g)
      ( cone-hom-arrow f g (hom-arrow-equiv-arrow f g α))
      ( is-equiv-map-codomain-equiv-arrow f g α)
      ( is-equiv-map-domain-equiv-arrow f g α)

  cartesian-hom-arrow-equiv-arrow : cartesian-hom-arrow f g
  pr1 cartesian-hom-arrow-equiv-arrow = hom-arrow-equiv-arrow f g α
  pr2 cartesian-hom-arrow-equiv-arrow = is-cartesian-equiv-arrow
```
