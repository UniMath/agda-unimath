# Directed graph duality

```agda
module graph-theory.directed-graph-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.small-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-duality
open import foundation.universe-levels

open import graph-theory.dependent-coproducts-directed-graphs
open import graph-theory.dependent-directed-graphs
open import graph-theory.directed-graphs
open import graph-theory.fibers-morphisms-directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Idea

{{#concept "Directed graph duality}} is an [equivalence](foundation-core.equivalences.md) between [dependent directed graphs](graph-theory.dependent-directed-graphs.md) over a [directed graph](graph-theory.directed-graphs.md) `G` and [morphisms of directed graphs](graph-theory.morphisms-directed-graphs.md) into `G`. This result is analogous to [type duality](foundation.type-duality.md), which asserts that type families over a type `A` are equivalently described as maps into `A`.

## Definitions

### The underlying map of the duality theorem for directed graphs

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  map-duality-Directed-Graph :
    {l3 l4 : Level} →
    Σ (Directed-Graph l3 l4) (λ H → hom-Directed-Graph H G) →
    Dependent-Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4) G
  map-duality-Directed-Graph (H , f) = fiber-hom-Directed-Graph H G f

  map-inv-duality-Directed-Graph :
    {l3 l4 : Level} →
    Dependent-Directed-Graph l3 l4 G →
    Σ ( Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4)) (λ H → hom-Directed-Graph H G)
  pr1 (map-inv-duality-Directed-Graph H) = Σ-Directed-Graph H
  pr2 (map-inv-duality-Directed-Graph H) = pr1-Σ-Directed-Graph H

  duality-Directed-Graph :
    {l3 l4 : Level} →
    Σ ( Directed-Graph (l1 ⊔ l3) {!!}) (λ H → hom-Directed-Graph H G) ≃
    Dependent-Directed-Graph (l1 ⊔ l3) {!!} G
  duality-Directed-Graph {l3} {l4} =
    ( equiv-Σ
      ( {!!})
      ( type-duality (is-small-lmax l3 (vertex-Directed-Graph G)))
      ( λ (H₀ , f₀) → {!!})) ∘e
    ( interchange-Σ-Σ _)

```
