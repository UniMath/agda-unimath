# Dependent reflexive graphs

```agda
module graph-theory.dependent-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
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
- A family of elements `refl B : (x : A₀) (y : B₀ x) → B₁ (refl A x) y y`
  witnessing the reflexivity of `B₁` over the reflexivity `refl A` of `A₁`.

To see that this is a sensible definition of dependent reflexive graphs, observe
that the type of reflexive graphs itself is
[equivalent](foundation-core.equivalences.md) to the type of dependent reflexive
graphs over the
[terminal reflexive graph](graph-theory.terminal-reflexive-graphs.md).
Furthermore, [graph homomorphisms](graph-theory.morphisms-reflexive-graphs.md)
into the [universal reflexive graph](graph-theory.universal-reflexive-graph.md)
are equivalent to dependent reflexive graphs.

Alternatively, a dependent reflexive graph `B` over `A` can be defined by

- A family `B₀ : A₀ → Reflexive-Graph` of reflexive graphs as the type family of
  vertices
- A family `B₁ : {x y : A₀} → A₁ x y → (B₀ x)₀ → (B₀ y)₀ → 𝒰`.
- A [family of equivalences](foundation.families-of-equivalences.md)
  `refl B : (x : A₀) (y y' : B₀ x) → B₁ (refl A x) y y' ≃ (B₀ x)₁ y y'`.

This definition is more closely related to the concept of morphism into the
universal reflexive graph.

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

### An equivalent definition of dependent reflexive graphs

The second definition of dependent reflexive graphs is more closely equivalent
to the concept of morphisms into the
[universal reflexive graph](graph-theory.universal-reflexive-graph.md).

```agda
Dependent-Reflexive-Graph' :
  {l1 l2 : Level} (l3 l4 : Level) → Reflexive-Graph l1 l2 →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Dependent-Reflexive-Graph' l3 l4 G =
  Σ ( Σ ( vertex-Reflexive-Graph G → Reflexive-Graph l3 l4)
        ( λ H →
          (x y : vertex-Reflexive-Graph G)
          (e : edge-Reflexive-Graph G x y) →
          vertex-Reflexive-Graph (H x) → vertex-Reflexive-Graph (H y) → UU l4))
    ( λ (H₀ , H₁) →
      (x : vertex-Reflexive-Graph G)
      (u v : vertex-Reflexive-Graph (H₀ x)) →
      H₁ x x (refl-Reflexive-Graph G x) u v ≃
      edge-Reflexive-Graph (H₀ x) u v)
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

### Evaluating dependent reflexive graphs at a point

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G) (x : vertex-Reflexive-Graph G)
  where

  ev-point-Dependent-Reflexive-Graph : Reflexive-Graph l3 l4
  pr1 (pr1 ev-point-Dependent-Reflexive-Graph) =
    vertex-Dependent-Reflexive-Graph H x
  pr2 (pr1 ev-point-Dependent-Reflexive-Graph) =
    edge-Dependent-Reflexive-Graph H (refl-Reflexive-Graph G x)
  pr2 ev-point-Dependent-Reflexive-Graph =
    refl-Dependent-Reflexive-Graph H
```

## See also

- The [universal reflexive graph](graph-theory.universal-reflexive-graph.md)
- [base change of dependent reflexive graphs](graph-theory.base-change-dependent-reflexive-graphs.md)
