# Morphisms of double arrows

```agda
module foundation.morphisms-double-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.function-types
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "morphism of double arrows" Disambiguation="between types" Agda=hom-double-arrow}}
from a [double arrow](foundation.double-arrows.md) `f, g : A → B` to a double
arrow `h, k : X → Y` is a pair of maps `i : A → X` and `j : B → Y`, such that
the squares

```text
           i                   i
     A ────────> X       A ────────> X
     │           │       │           │
   f │           │ h   g │           │ k
     │           │       │           │
     ∨           ∨       ∨           ∨
     B ────────> Y       B ────────> Y
           j                   j
```

[commute](foundation-core.commuting-squares-of-maps.md). The map `i` is referred
to as the _domain map_, and the `j` as the _codomain map_.

Alternatively, a morphism of double arrows is a pair of
[morphisms of arrows](foundation.morphisms-arrows.md) `f → h` and `g → k` that
share the underlying maps.

## Definitions

### Morphisms of double arrows

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  where

  left-coherence-hom-double-arrow :
    (domain-double-arrow a → domain-double-arrow a') →
    (codomain-double-arrow a → codomain-double-arrow a') →
    UU (l1 ⊔ l4)
  left-coherence-hom-double-arrow hA hB =
    coherence-square-maps
      ( hA)
      ( left-map-double-arrow a)
      ( left-map-double-arrow a')
      ( hB)

  right-coherence-hom-double-arrow :
    (domain-double-arrow a → domain-double-arrow a') →
    (codomain-double-arrow a → codomain-double-arrow a') →
    UU (l1 ⊔ l4)
  right-coherence-hom-double-arrow hA hB =
    coherence-square-maps
      ( hA)
      ( right-map-double-arrow a)
      ( right-map-double-arrow a')
      ( hB)

  hom-double-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-double-arrow =
    Σ ( domain-double-arrow a → domain-double-arrow a')
      ( λ hA →
        Σ ( codomain-double-arrow a → codomain-double-arrow a')
          ( λ hB →
            left-coherence-hom-double-arrow hA hB ×
            right-coherence-hom-double-arrow hA hB))
```

### Components of a morphism of double arrows

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  (h : hom-double-arrow a a')
  where

  domain-map-hom-double-arrow : domain-double-arrow a → domain-double-arrow a'
  domain-map-hom-double-arrow = pr1 h

  codomain-map-hom-double-arrow :
    codomain-double-arrow a → codomain-double-arrow a'
  codomain-map-hom-double-arrow = pr1 (pr2 h)

  left-square-hom-double-arrow :
    left-coherence-hom-double-arrow a a'
      ( domain-map-hom-double-arrow)
      ( codomain-map-hom-double-arrow)
  left-square-hom-double-arrow = pr1 (pr2 (pr2 h))

  left-hom-arrow-hom-double-arrow :
    hom-arrow (left-map-double-arrow a) (left-map-double-arrow a')
  pr1 left-hom-arrow-hom-double-arrow =
    domain-map-hom-double-arrow
  pr1 (pr2 left-hom-arrow-hom-double-arrow) =
    codomain-map-hom-double-arrow
  pr2 (pr2 left-hom-arrow-hom-double-arrow) =
    left-square-hom-double-arrow

  right-square-hom-double-arrow :
    right-coherence-hom-double-arrow a a'
      ( domain-map-hom-double-arrow)
      ( codomain-map-hom-double-arrow)
  right-square-hom-double-arrow = pr2 (pr2 (pr2 h))

  right-hom-arrow-hom-double-arrow :
    hom-arrow (right-map-double-arrow a) (right-map-double-arrow a')
  pr1 right-hom-arrow-hom-double-arrow =
    domain-map-hom-double-arrow
  pr1 (pr2 right-hom-arrow-hom-double-arrow) =
    codomain-map-hom-double-arrow
  pr2 (pr2 right-hom-arrow-hom-double-arrow) =
    right-square-hom-double-arrow
```

### The identity morphism of double arrows

```agda
module _
  {l1 l2 : Level} (a : double-arrow l1 l2)
  where

  id-hom-double-arrow : hom-double-arrow a a
  pr1 id-hom-double-arrow = id
  pr1 (pr2 id-hom-double-arrow) = id
  pr2 (pr2 id-hom-double-arrow) = (refl-htpy , refl-htpy)
```

### Composition of morphisms of double arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (a : double-arrow l1 l2) (b : double-arrow l3 l4) (c : double-arrow l5 l6)
  (g : hom-double-arrow b c) (f : hom-double-arrow a b)
  where

  domain-map-comp-hom-double-arrow :
    domain-double-arrow a → domain-double-arrow c
  domain-map-comp-hom-double-arrow =
    domain-map-hom-double-arrow b c g ∘ domain-map-hom-double-arrow a b f

  codomain-map-comp-hom-double-arrow :
    codomain-double-arrow a → codomain-double-arrow c
  codomain-map-comp-hom-double-arrow =
    codomain-map-hom-double-arrow b c g ∘ codomain-map-hom-double-arrow a b f

  left-square-comp-hom-double-arrow :
    left-coherence-hom-double-arrow a c
      ( domain-map-comp-hom-double-arrow)
      ( codomain-map-comp-hom-double-arrow)
  left-square-comp-hom-double-arrow =
    coh-comp-hom-arrow
      ( left-map-double-arrow a)
      ( left-map-double-arrow b)
      ( left-map-double-arrow c)
      ( left-hom-arrow-hom-double-arrow b c g)
      ( left-hom-arrow-hom-double-arrow a b f)

  right-square-comp-hom-double-arrow :
    right-coherence-hom-double-arrow a c
      ( domain-map-comp-hom-double-arrow)
      ( codomain-map-comp-hom-double-arrow)
  right-square-comp-hom-double-arrow =
    coh-comp-hom-arrow
      ( right-map-double-arrow a)
      ( right-map-double-arrow b)
      ( right-map-double-arrow c)
      ( right-hom-arrow-hom-double-arrow b c g)
      ( right-hom-arrow-hom-double-arrow a b f)

  comp-hom-double-arrow : hom-double-arrow a c
  pr1 comp-hom-double-arrow =
    domain-map-comp-hom-double-arrow
  pr1 (pr2 comp-hom-double-arrow) =
    codomain-map-comp-hom-double-arrow
  pr1 (pr2 (pr2 comp-hom-double-arrow)) =
    left-square-comp-hom-double-arrow
  pr2 (pr2 (pr2 comp-hom-double-arrow)) =
    right-square-comp-hom-double-arrow
```
