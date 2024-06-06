# Morphisms of twisted arrows

```agda
module foundation.morphisms-twisted-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A **morphism of twisted arrows** from `f : A → B` to `g : X → Y` is a triple
`(i , j , H)` consisting of

- a map `i : X → A`
- a map `j : B → Y`, and
- a [homotopy](foundation-core.homotopies.md) `H : j ∘ f ∘ i ~ g` witnessing
  that the square

  ```text
           i
      A <───── X
      │        │
    f │        │ g
      ∨        ∨
      B ─────> Y
          j
  ```

  commutes.

Thus, a morphism of twisted arrows can also be understood as _a factorization of
`g` through `f`_.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  coherence-hom-twisted-arrow :
    (X → A) → (B → Y) → UU (l3 ⊔ l4)
  coherence-hom-twisted-arrow i j = j ∘ f ∘ i ~ g

  hom-twisted-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-twisted-arrow =
    Σ (X → A) (λ i → Σ (B → Y) (coherence-hom-twisted-arrow i))

  module _
    (α : hom-twisted-arrow)
    where

    map-domain-hom-twisted-arrow : X → A
    map-domain-hom-twisted-arrow = pr1 α

    map-codomain-hom-twisted-arrow : B → Y
    map-codomain-hom-twisted-arrow = pr1 (pr2 α)

    coh-hom-twisted-arrow :
      map-codomain-hom-twisted-arrow ∘ f ∘ map-domain-hom-twisted-arrow ~ g
    coh-hom-twisted-arrow = pr2 (pr2 α)
```

## See also

- [Morphisms of arrows](foundation.morphisms-arrows.md).
