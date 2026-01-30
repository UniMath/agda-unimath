# Equivalences of double arrows

```agda
module foundation.equivalences-double-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.homotopies
open import foundation.morphisms-double-arrows
open import foundation.universe-levels

open import foundation-core.equivalences-arrows
```

</details>

## Idea

An
{{#concept "equivalence of double arrows" Disambiguation="between types" Agda=equiv-double-arrow}}
from a [double arrow](foundation.double-arrows.md) `f, g : A → B` to a double
arrow `h, k : X → Y` is a pair of
[equivalences](foundation-core.equivalences.md) `i : A ≃ X` and `j : B ≃ Y`,
such that the squares

```text
           i                   i
     A --------> X       A --------> X
     |     ≃     |       |     ≃     |
   f |           | h   g |           | k
     |           |       |           |
     ∨     ≃     ∨       ∨     ≃     ∨
     B --------> Y       B --------> Y
           j                   j
```

[commute](foundation-core.commuting-squares-of-maps.md). The equivalence `i` is
referred to as the _domain equivalence_, and the `j` as the _codomain
equivalence_.

Alternatively, an equivalence of double arrows is a pair of
[equivalences of arrows](foundation-core.equivalences-arrows.md) `f ≃ h` and
`g ≃ k` that share the underlying maps.

## Definitions

### Equivalences of double arrows

```agda
module _
  {l1 l2 l3 l4 : Level}
  (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  where

  left-coherence-equiv-double-arrow :
    (domain-double-arrow a ≃ domain-double-arrow a') →
    (codomain-double-arrow a ≃ codomain-double-arrow a') →
    UU (l1 ⊔ l4)
  left-coherence-equiv-double-arrow eA eB =
    left-coherence-hom-double-arrow a a' (map-equiv eA) (map-equiv eB)

  right-coherence-equiv-double-arrow :
    (domain-double-arrow a ≃ domain-double-arrow a') →
    (codomain-double-arrow a ≃ codomain-double-arrow a') →
    UU (l1 ⊔ l4)
  right-coherence-equiv-double-arrow eA eB =
    right-coherence-hom-double-arrow a a' (map-equiv eA) (map-equiv eB)

  equiv-double-arrow :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-double-arrow =
    Σ ( domain-double-arrow a ≃ domain-double-arrow a')
      ( λ eA →
        Σ ( codomain-double-arrow a ≃ codomain-double-arrow a')
          ( λ eB →
            left-coherence-equiv-double-arrow eA eB ×
            right-coherence-equiv-double-arrow eA eB))
```

### Components of an equivalence of double arrows

```agda
module _
  {l1 l2 l3 l4 : Level}
  (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  (e : equiv-double-arrow a a')
  where

  domain-equiv-equiv-double-arrow :
    domain-double-arrow a ≃ domain-double-arrow a'
  domain-equiv-equiv-double-arrow = pr1 e

  domain-map-equiv-double-arrow :
    domain-double-arrow a → domain-double-arrow a'
  domain-map-equiv-double-arrow = map-equiv domain-equiv-equiv-double-arrow

  is-equiv-domain-map-equiv-double-arrow :
    is-equiv domain-map-equiv-double-arrow
  is-equiv-domain-map-equiv-double-arrow =
    is-equiv-map-equiv domain-equiv-equiv-double-arrow

  codomain-equiv-equiv-double-arrow :
    codomain-double-arrow a ≃ codomain-double-arrow a'
  codomain-equiv-equiv-double-arrow = pr1 (pr2 e)

  codomain-map-equiv-double-arrow :
    codomain-double-arrow a → codomain-double-arrow a'
  codomain-map-equiv-double-arrow = map-equiv codomain-equiv-equiv-double-arrow

  is-equiv-codomain-map-equiv-double-arrow :
    is-equiv codomain-map-equiv-double-arrow
  is-equiv-codomain-map-equiv-double-arrow =
    is-equiv-map-equiv codomain-equiv-equiv-double-arrow

  left-square-equiv-double-arrow :
    left-coherence-equiv-double-arrow a a'
      ( domain-equiv-equiv-double-arrow)
      ( codomain-equiv-equiv-double-arrow)
  left-square-equiv-double-arrow = pr1 (pr2 (pr2 e))

  left-equiv-arrow-equiv-double-arrow :
    equiv-arrow (left-map-double-arrow a) (left-map-double-arrow a')
  pr1 left-equiv-arrow-equiv-double-arrow =
    domain-equiv-equiv-double-arrow
  pr1 (pr2 left-equiv-arrow-equiv-double-arrow) =
    codomain-equiv-equiv-double-arrow
  pr2 (pr2 left-equiv-arrow-equiv-double-arrow) =
    left-square-equiv-double-arrow

  right-square-equiv-double-arrow :
    right-coherence-equiv-double-arrow a a'
      ( domain-equiv-equiv-double-arrow)
      ( codomain-equiv-equiv-double-arrow)
  right-square-equiv-double-arrow = pr2 (pr2 (pr2 e))

  right-equiv-arrow-equiv-double-arrow :
    equiv-arrow (right-map-double-arrow a) (right-map-double-arrow a')
  pr1 right-equiv-arrow-equiv-double-arrow =
    domain-equiv-equiv-double-arrow
  pr1 (pr2 right-equiv-arrow-equiv-double-arrow) =
    codomain-equiv-equiv-double-arrow
  pr2 (pr2 right-equiv-arrow-equiv-double-arrow) =
    right-square-equiv-double-arrow

  hom-equiv-double-arrow : hom-double-arrow a a'
  pr1 hom-equiv-double-arrow =
    domain-map-equiv-double-arrow
  pr1 (pr2 hom-equiv-double-arrow) =
    codomain-map-equiv-double-arrow
  pr1 (pr2 (pr2 hom-equiv-double-arrow)) =
    left-square-equiv-double-arrow
  pr2 (pr2 (pr2 hom-equiv-double-arrow)) =
    right-square-equiv-double-arrow
```

### Equivalences of double arrows induced by morphisms of double arrows whose maps are equivalences

Given a [morphism of double arrows](foundation.morphisms-double-arrows.md)

```text
           i                   i
     A --------> X       A --------> X
     |           |       |           |
   f |           | h   g |           | k
     |           |       |           |
     ∨           ∨       ∨           ∨
     B --------> Y       B --------> Y ,
           j                   j
```

it suffices to show that `i` and `j` are equivalences to obtain an equivalence
of double arrows.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  where

  equiv-hom-double-arrow :
    (h : hom-double-arrow a a') →
    is-equiv (domain-map-hom-double-arrow a a' h) →
    is-equiv (codomain-map-hom-double-arrow a a' h) →
    equiv-double-arrow a a'
  pr1 (equiv-hom-double-arrow h is-equiv-dom _) =
    (domain-map-hom-double-arrow a a' h , is-equiv-dom)
  pr1 (pr2 (equiv-hom-double-arrow h _ is-equiv-cod)) =
    codomain-map-hom-double-arrow a a' h , is-equiv-cod
  pr2 (pr2 (equiv-hom-double-arrow h _ _)) =
    (left-square-hom-double-arrow a a' h , right-square-hom-double-arrow a a' h)
```

### The identity equivalence of double arrows

```agda
module _
  {l1 l2 : Level} (a : double-arrow l1 l2)
  where

  id-equiv-double-arrow : equiv-double-arrow a a
  pr1 id-equiv-double-arrow = id-equiv
  pr1 (pr2 id-equiv-double-arrow) = id-equiv
  pr2 (pr2 id-equiv-double-arrow) = (refl-htpy , refl-htpy)
```

### Composition of equivalences of double arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (a : double-arrow l1 l2) (b : double-arrow l3 l4) (c : double-arrow l5 l6)
  (f : equiv-double-arrow b c) (e : equiv-double-arrow a b)
  where

  comp-equiv-double-arrow : equiv-double-arrow a c
  comp-equiv-double-arrow =
    equiv-hom-double-arrow a c
      ( comp-hom-double-arrow a b c
        ( hom-equiv-double-arrow b c f)
        ( hom-equiv-double-arrow a b e))
      ( is-equiv-comp _ _
        ( is-equiv-domain-map-equiv-double-arrow a b e)
        ( is-equiv-domain-map-equiv-double-arrow b c f))
      ( is-equiv-comp _ _
        ( is-equiv-codomain-map-equiv-double-arrow a b e)
        ( is-equiv-codomain-map-equiv-double-arrow b c f))

  domain-equiv-comp-equiv-double-arrow :
    domain-double-arrow a ≃ domain-double-arrow c
  domain-equiv-comp-equiv-double-arrow =
    domain-equiv-equiv-double-arrow a c comp-equiv-double-arrow

  codomain-equiv-comp-equiv-double-arrow :
    codomain-double-arrow a ≃ codomain-double-arrow c
  codomain-equiv-comp-equiv-double-arrow =
    codomain-equiv-equiv-double-arrow a c comp-equiv-double-arrow

  left-square-comp-equiv-double-arrow :
    left-coherence-equiv-double-arrow a c
      ( domain-equiv-comp-equiv-double-arrow)
      ( codomain-equiv-comp-equiv-double-arrow)
  left-square-comp-equiv-double-arrow =
    left-square-equiv-double-arrow a c comp-equiv-double-arrow

  right-square-comp-equiv-double-arrow :
    right-coherence-equiv-double-arrow a c
      ( domain-equiv-comp-equiv-double-arrow)
      ( codomain-equiv-comp-equiv-double-arrow)
  right-square-comp-equiv-double-arrow =
    right-square-equiv-double-arrow a c comp-equiv-double-arrow
```
