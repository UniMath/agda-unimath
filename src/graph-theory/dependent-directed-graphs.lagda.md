# Dependent directed graphs

```agda
module graph-theory.dependent-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.directed-graphs
```

</details>

## Idea

Consider a [directed graph](graph-theory.directed-graphs.md) `A`. A
{{#concept "dependent directed graph}} `B` over `A` consists of:

- A family `B₀ : A₀ → 𝒰` of vertices
- A family `B₁ : (x y : A₀) → A₁ x y → B₀ x → B₀ y → 𝒰` of
  [binary relations](foundation.binary-relations.md) between the types of
  vertices `B₀`, indexed by the type of edges `A₁` in `A`.

This definition may appear overly general. However, one can observe that the
type of directed graphs itself is [equivalent](foundation-core.equivalences.md)
to the type of dependent directed graphs over the
[terminal directed graph](graph-theory.terminal-directed-graphs.md).
Furthermore, [graph homomorphisms](graph-theory.morphisms-directed-graphs.md)
into the [universal directed graph](graph-theory.universal-directed-graph.md)
are equivalent to dependent directed graphs.

## Definitions

### Dependent directed graphs

```agda
Dependent-Directed-Graph :
  {l1 l2 : Level} (l3 l4 : Level) → Directed-Graph l1 l2 →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Dependent-Directed-Graph l3 l4 A =
  Σ ( vertex-Directed-Graph A → UU l3)
    ( λ B₀ →
      (x y : vertex-Directed-Graph A) →
      edge-Directed-Graph A x y → B₀ x → B₀ y → UU l4)

module _
  {l1 l2 l3 l4 : Level} {A : Directed-Graph l1 l2}
  (B : Dependent-Directed-Graph l3 l4 A)
  where

  vertex-Dependent-Directed-Graph : vertex-Directed-Graph A → UU l3
  vertex-Dependent-Directed-Graph = pr1 B

  edge-Dependent-Directed-Graph :
    {x y : vertex-Directed-Graph A} →
    edge-Directed-Graph A x y →
    vertex-Dependent-Directed-Graph x →
    vertex-Dependent-Directed-Graph y → UU l4
  edge-Dependent-Directed-Graph = pr2 B _ _
```

### Constant dependent directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Directed-Graph l1 l2) (B : Directed-Graph l3 l4)
  where

  vertex-constant-Dependent-Directed-Graph :
    vertex-Directed-Graph A → UU l3
  vertex-constant-Dependent-Directed-Graph x = vertex-Directed-Graph B

  edge-constant-Dependent-Directed-Graph :
    {x y : vertex-Directed-Graph A} →
    edge-Directed-Graph A x y →
    vertex-constant-Dependent-Directed-Graph x →
    vertex-constant-Dependent-Directed-Graph y → UU l4
  edge-constant-Dependent-Directed-Graph e =
    edge-Directed-Graph B

  constant-Dependent-Directed-Graph : Dependent-Directed-Graph l3 l4 A
  pr1 constant-Dependent-Directed-Graph =
    vertex-constant-Dependent-Directed-Graph
  pr2 constant-Dependent-Directed-Graph _ _ =
    edge-constant-Dependent-Directed-Graph
```

## See also

- The [universal directed graph](graph-theory.universal-directed-graph.md)
- [Pullbacks of dependent directed graphs](graph-theory.pullbacks-dependent-directed-graphs.md)
