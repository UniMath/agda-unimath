# Dependent reflexive graphs

```agda
module graph-theory.dependent-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.dependent-directed-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

Consider a [reflexive graph](graph-theory.reflexive-graphs.md) `A`. A
{{#concept "dependent reflexive graph" Agda=Dependent-Reflexive-Graph}} `B` over
`A` consists of:

- A family `B₀ : A₀ → 𝒰` of types as the type family of vertices
- A family `B₁ : {x y : A₀} → A₁ x y → B₀ x → B₀ y → 𝒰` of
  [binary relations](foundation.binary-relations.md) between the types of
  vertices `B₀`, indexed by the type of edges `A₁` in `A`.
- A family of elements `Bᵣ : (x : A₀) (y : B₀ x) → B₁ (Aᵣ x) y y` witnessing the
  reflexivity of `B₁` over the reflexivity `Aᵣ` of `A₁`.

This definition may appear overly general. However, one can observe that the
type of reflexive graphs itself is [equivalent](foundation-core.equivalences.md)
to the type of dependent reflexive graphs over the
[terminal reflexive graph](graph-theory.terminal-reflexive-graphs.md).
Furthermore, [graph homomorphisms](graph-theory.morphisms-reflexive-graphs.md)
into the [universal reflexive graph](graph-theory.universal-reflexive-graph.md)
are equivalent to dependent reflexive graphs.

Alternatively, a dependent reflexive graph `B` over `A` can be defined by

- A family `B₀ : A₀ → Reflexive-Graph` of reflexive graphs as the type family of
  vertices
- A family `B₁ : {x y : A₀} → A₁ x y → (B₀ x)₀ → (B₀ y)₀ → 𝒰`.
- A family `Bᵣ : (x : A₀) → B₁ (Aᵣ x) ＝ (B₀ x)₁

## Definitions

### Dependent reflexive graphs

```agda
Dependent-Reflexive-Graph :
  {l1 l2 : Level} (l3 l4 : Level) → Reflexive-Graph l1 l2 →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Dependent-Reflexive-Graph l3 l4 A =
  Σ ( Dependent-Directed-Graph l3 l4 (directed-graph-Reflexive-Graph A))
    ( λ B →
      (x : vertex-Reflexive-Graph A) (y : vertex-Dependent-Directed-Graph B x) →
      edge-Dependent-Directed-Graph B (refl-Reflexive-Graph A x) y y)

module _
  {l1 l2 l3 l4 : Level} {A : Reflexive-Graph l1 l2}
  (B : Dependent-Reflexive-Graph l3 l4 A)
  where

  dependent-directed-graph-Dependent-Reflexive-Graph :
    Dependent-Directed-Graph l3 l4 (directed-graph-Reflexive-Graph A)
  dependent-directed-graph-Dependent-Reflexive-Graph = pr1 B

  vertex-Dependent-Reflexive-Graph :
    vertex-Reflexive-Graph A → UU l3
  vertex-Dependent-Reflexive-Graph =
    vertex-Dependent-Directed-Graph
      dependent-directed-graph-Dependent-Reflexive-Graph

  edge-Dependent-Reflexive-Graph :
    {x y : vertex-Reflexive-Graph A} →
    edge-Reflexive-Graph A x y →
    vertex-Dependent-Reflexive-Graph x →
    vertex-Dependent-Reflexive-Graph y → UU l4
  edge-Dependent-Reflexive-Graph =
    edge-Dependent-Directed-Graph
      dependent-directed-graph-Dependent-Reflexive-Graph

  refl-Dependent-Reflexive-Graph :
    {x : vertex-Reflexive-Graph A} (y : vertex-Dependent-Reflexive-Graph x) →
    edge-Dependent-Reflexive-Graph (refl-Reflexive-Graph A x) y y
  refl-Dependent-Reflexive-Graph = pr2 B _
```

### Constant dependent reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Reflexive-Graph l1 l2) (B : Reflexive-Graph l3 l4)
  where

  vertex-constant-Dependent-Reflexive-Graph :
    vertex-Reflexive-Graph A → UU l3
  vertex-constant-Dependent-Reflexive-Graph x = vertex-Reflexive-Graph B

  edge-constant-Dependent-Reflexive-Graph :
    {x y : vertex-Reflexive-Graph A} →
    edge-Reflexive-Graph A x y →
    vertex-constant-Dependent-Reflexive-Graph x →
    vertex-constant-Dependent-Reflexive-Graph y → UU l4
  edge-constant-Dependent-Reflexive-Graph _ =
    edge-Reflexive-Graph B

  refl-constant-Dependent-Reflexive-Graph :
    (x : vertex-Reflexive-Graph A)
    (y : vertex-constant-Dependent-Reflexive-Graph x) →
    edge-constant-Dependent-Reflexive-Graph (refl-Reflexive-Graph A x) y y
  refl-constant-Dependent-Reflexive-Graph _ =
    refl-Reflexive-Graph B

  constant-Dependent-Reflexive-Graph : Dependent-Reflexive-Graph l3 l4 A
  pr1 (pr1 constant-Dependent-Reflexive-Graph) =
    vertex-constant-Dependent-Reflexive-Graph
  pr2 (pr1 constant-Dependent-Reflexive-Graph) _ _ =
    edge-constant-Dependent-Reflexive-Graph
  pr2 constant-Dependent-Reflexive-Graph =
    refl-constant-Dependent-Reflexive-Graph
```

## See also

- The [universal reflexive graph](graph-theory.universal-reflexive-graph.md)
- [Pullbacks of dependent reflexive graphs](graph-theory.pullbacks-dependent-reflexive-graphs.md)
