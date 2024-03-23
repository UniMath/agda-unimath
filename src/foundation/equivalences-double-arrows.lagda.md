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
open import foundation.morphisms-double-arrows
open import foundation.universe-levels
```

</details>

## Idea

TODO

## Definitions

### Equivalences of double arrows

```agda
module _
  {l1 l2 l3 l4 : Level}
  (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  where

  bottom-coherence-equiv-double-arrow :
    (domain-double-arrow a ≃ domain-double-arrow a') →
    (codomain-double-arrow a ≃ codomain-double-arrow a') →
    UU (l1 ⊔ l4)
  bottom-coherence-equiv-double-arrow eA eB =
    bottom-coherence-hom-double-arrow a a' (map-equiv eA) (map-equiv eB)

  top-coherence-equiv-double-arrow :
    (domain-double-arrow a ≃ domain-double-arrow a') →
    (codomain-double-arrow a ≃ codomain-double-arrow a') →
    UU (l1 ⊔ l4)
  top-coherence-equiv-double-arrow eA eB =
    top-coherence-hom-double-arrow a a' (map-equiv eA) (map-equiv eB)

  equiv-double-arrow :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-double-arrow =
    Σ ( domain-double-arrow a ≃ domain-double-arrow a')
      ( λ eA →
        Σ ( codomain-double-arrow a ≃ codomain-double-arrow a')
          ( λ eB →
            bottom-coherence-equiv-double-arrow eA eB ×
            top-coherence-equiv-double-arrow eA eB))
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

  bottom-coherence-square-equiv-double-arrow :
    bottom-coherence-equiv-double-arrow a a'
      ( domain-equiv-equiv-double-arrow)
      ( codomain-equiv-equiv-double-arrow)
  bottom-coherence-square-equiv-double-arrow = pr1 (pr2 (pr2 e))

  top-coherence-square-equiv-double-arrow :
    top-coherence-equiv-double-arrow a a'
      ( domain-equiv-equiv-double-arrow)
      ( codomain-equiv-equiv-double-arrow)
  top-coherence-square-equiv-double-arrow = pr2 (pr2 (pr2 e))

  hom-double-arrow-equiv-double-arrow : hom-double-arrow a a'
  pr1 hom-double-arrow-equiv-double-arrow =
    domain-map-equiv-double-arrow
  pr1 (pr2 hom-double-arrow-equiv-double-arrow) =
    codomain-map-equiv-double-arrow
  pr1 (pr2 (pr2 hom-double-arrow-equiv-double-arrow)) =
    bottom-coherence-square-equiv-double-arrow
  pr2 (pr2 (pr2 hom-double-arrow-equiv-double-arrow)) =
    top-coherence-square-equiv-double-arrow
```
