# Morphisms of arrows obtained from diagonal maps

```agda
module orthogonal-factorization-systems.morphisms-arrows-from-diagonal-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

Consider a pair of maps `f : A → B` and `g : X → Y`. Then there is an operation `hom-arrow-map` that takes any `j : B → X` as in the diagram

```text
    A       X
    |     ∧ |
  f |  j/   | g
    ∨ /     ∨
    B       Y
```

to a [morphism of arrows](foundation.morphisms-arrows.md) from `f` to `g` as in the diagram

```text
         j ∘ f
    A ----------> X
    |             |
  f |  refl-htpy  | g
    ∨             ∨
    B ----------> Y.
         g ∘ j
```

This operation is studied in [Lifting squares](orthogonal-factorization-systems.lifting-squares.md).

## Definitions

### Morphisms of arrows obtained from diagonal maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  map-domain-hom-arrow-map : (B → X) → A → X
  map-domain-hom-arrow-map j = j ∘ f

  map-codomain-hom-arrow-map : (B → X) → B → Y
  map-codomain-hom-arrow-map j = g ∘ j

  coh-hom-arrow-map :
    (j : B → X) →
    coherence-hom-arrow f g
      ( map-domain-hom-arrow-map j)
      ( map-codomain-hom-arrow-map j)
  coh-hom-arrow-map j = refl-htpy

  hom-arrow-map : (B → X) → hom-arrow f g
  pr1 (hom-arrow-map j) = map-domain-hom-arrow-map j
  pr1 (pr2 (hom-arrow-map j)) = map-codomain-hom-arrow-map j
  pr2 (pr2 (hom-arrow-map j)) = coh-hom-arrow-map j
```

### The action on homotopies of `hom-arrow-map`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) {j k : B → X} (H : j ~ k)
  where

  htpy-domain-htpy-hom-arrow-htpy :
    map-domain-hom-arrow-map f g j ~ map-domain-hom-arrow-map f g k
  htpy-domain-htpy-hom-arrow-htpy = H ·r f

  htpy-codomain-htpy-hom-arrow-htpy :
    map-codomain-hom-arrow-map f g j ~ map-codomain-hom-arrow-map f g k
  htpy-codomain-htpy-hom-arrow-htpy = g ·l H

  coh-htpy-hom-arrow-htpy :
    coherence-htpy-hom-arrow f g
      ( hom-arrow-map f g j)
      ( hom-arrow-map f g k)
      ( htpy-domain-htpy-hom-arrow-htpy)
      ( htpy-codomain-htpy-hom-arrow-htpy)
  coh-htpy-hom-arrow-htpy = inv-htpy right-unit-htpy

  htpy-hom-arrow-htpy :
    htpy-hom-arrow f g (hom-arrow-map f g j) (hom-arrow-map f g k)
  pr1 htpy-hom-arrow-htpy = htpy-domain-htpy-hom-arrow-htpy
  pr1 (pr2 htpy-hom-arrow-htpy) = htpy-codomain-htpy-hom-arrow-htpy
  pr2 (pr2 htpy-hom-arrow-htpy) = coh-htpy-hom-arrow-htpy
```
