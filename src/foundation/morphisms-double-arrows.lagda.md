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
open import foundation.universe-levels
```

</details>

## Idea

TODO

## Definitions

### Morphisms of double arrows

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  where

  bottom-coherence-hom-double-arrow :
    (domain-double-arrow a → domain-double-arrow a') →
    (codomain-double-arrow a → codomain-double-arrow a') →
    UU (l1 ⊔ l4)
  bottom-coherence-hom-double-arrow hA hB =
    coherence-square-maps'
      ( bottom-map-double-arrow a)
      ( hA)
      ( hB)
      ( bottom-map-double-arrow a')

  top-coherence-hom-double-arrow :
    (domain-double-arrow a → domain-double-arrow a') →
    (codomain-double-arrow a → codomain-double-arrow a') →
    UU (l1 ⊔ l4)
  top-coherence-hom-double-arrow hA hB =
    coherence-square-maps'
      ( top-map-double-arrow a)
      ( hA)
      ( hB)
      ( top-map-double-arrow a')

  hom-double-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-double-arrow =
    Σ ( domain-double-arrow a → domain-double-arrow a')
      ( λ hA →
        Σ ( codomain-double-arrow a → codomain-double-arrow a')
          ( λ hB →
            bottom-coherence-hom-double-arrow hA hB ×
            top-coherence-hom-double-arrow hA hB))
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

  bottom-coherence-square-hom-double-arrow :
    bottom-coherence-hom-double-arrow a a'
      ( domain-map-hom-double-arrow)
      ( codomain-map-hom-double-arrow)
  bottom-coherence-square-hom-double-arrow = pr1 (pr2 (pr2 h))

  top-coherence-square-hom-double-arrow :
    top-coherence-hom-double-arrow a a'
      ( domain-map-hom-double-arrow)
      ( codomain-map-hom-double-arrow)
  top-coherence-square-hom-double-arrow = pr2 (pr2 (pr2 h))
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

  bottom-coherence-square-comp-hom-double-arrow :
    bottom-coherence-hom-double-arrow a c
      ( domain-map-comp-hom-double-arrow)
      ( codomain-map-comp-hom-double-arrow)
  bottom-coherence-square-comp-hom-double-arrow =
    pasting-horizontal-coherence-square-maps
      ( domain-map-hom-double-arrow a b f)
      ( domain-map-hom-double-arrow b c g)
      ( bottom-map-double-arrow a)
      ( bottom-map-double-arrow b)
      ( bottom-map-double-arrow c)
      ( codomain-map-hom-double-arrow a b f)
      ( codomain-map-hom-double-arrow b c g)
      ( bottom-coherence-square-hom-double-arrow a b f)
      ( bottom-coherence-square-hom-double-arrow b c g)

  top-coherence-square-comp-hom-double-arrow :
    top-coherence-hom-double-arrow a c
      ( domain-map-comp-hom-double-arrow)
      ( codomain-map-comp-hom-double-arrow)
  top-coherence-square-comp-hom-double-arrow =
    pasting-horizontal-coherence-square-maps
      ( domain-map-hom-double-arrow a b f)
      ( domain-map-hom-double-arrow b c g)
      ( top-map-double-arrow a)
      ( top-map-double-arrow b)
      ( top-map-double-arrow c)
      ( codomain-map-hom-double-arrow a b f)
      ( codomain-map-hom-double-arrow b c g)
      ( top-coherence-square-hom-double-arrow a b f)
      ( top-coherence-square-hom-double-arrow b c g)

  comp-hom-double-arrow : hom-double-arrow a c
  pr1 comp-hom-double-arrow =
    domain-map-comp-hom-double-arrow
  pr1 (pr2 comp-hom-double-arrow) =
    codomain-map-comp-hom-double-arrow
  pr1 (pr2 (pr2 comp-hom-double-arrow)) =
    bottom-coherence-square-comp-hom-double-arrow
  pr2 (pr2 (pr2 comp-hom-double-arrow)) =
    top-coherence-square-comp-hom-double-arrow
```
