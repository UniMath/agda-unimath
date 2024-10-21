# Directed graph duality

```agda
module graph-theory.directed-graph-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import graph-theory.dependent-coproducts-directed-graphs
open import graph-theory.dependent-directed-graphs
open import graph-theory.directed-graphs
open import graph-theory.equivalences-dependent-directed-graphs
open import graph-theory.equivalences-directed-graphs
open import graph-theory.fibers-morphisms-directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Idea

{{#concept "Directed graph duality" Agda=duality-Directed-Graph}} is an
[equivalence](foundation-core.equivalences.md) between
[dependent directed graphs](graph-theory.dependent-directed-graphs.md) over a
[directed graph](graph-theory.directed-graphs.md) `G` and
[morphisms of directed graphs](graph-theory.morphisms-directed-graphs.md) into
`G`. This result is analogous to [type duality](foundation.type-duality.md),
which asserts that type families over a type `A` are equivalently described as
maps into `A`.

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
```

### The inverse map of the duality theorem for directed graphs

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  map-inv-duality-Directed-Graph :
    {l3 l4 : Level} →
    Dependent-Directed-Graph l3 l4 G →
    Σ ( Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4)) (λ H → hom-Directed-Graph H G)
  pr1 (map-inv-duality-Directed-Graph H) = Σ-Directed-Graph H
  pr2 (map-inv-duality-Directed-Graph H) = pr1-Σ-Directed-Graph H
```

## Properties

### The directed graph duality theorem

#### Characterization of the identity type of the total space of morphisms into a directed graph

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  equiv-total-hom-Directed-Graph :
    {l3 l4 l5 l6 : Level} →
    (f : Σ (Directed-Graph l3 l4) (λ H → hom-Directed-Graph H G))
    (g : Σ (Directed-Graph l5 l6) (λ H → hom-Directed-Graph H G)) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  equiv-total-hom-Directed-Graph (H , f) (K , g) =
    Σ ( equiv-Directed-Graph H K)
      ( λ e →
        htpy-hom-Directed-Graph H G
          ( f)
          ( comp-hom-Directed-Graph H K G g (hom-equiv-Directed-Graph H K e)))

  id-equiv-total-hom-Directed-Graph :
    {l3 l4 : Level}
    (f : Σ (Directed-Graph l3 l4) (λ H → hom-Directed-Graph H G)) →
    equiv-total-hom-Directed-Graph f f
  pr1 (id-equiv-total-hom-Directed-Graph (H , f)) = id-equiv-Directed-Graph H
  pr2 (id-equiv-total-hom-Directed-Graph (H , f)) =
    right-unit-law-comp-hom-Directed-Graph H G f

  is-torsorial-equiv-total-hom-Directed-Graph :
    {l3 l4 : Level}
    (f : Σ (Directed-Graph l3 l4) (λ H → hom-Directed-Graph H G)) →
    is-torsorial (equiv-total-hom-Directed-Graph {l5 = l3} {l6 = l4} f)
  is-torsorial-equiv-total-hom-Directed-Graph (H , f) =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-Directed-Graph H)
      ( H , id-equiv-Directed-Graph H)
      ( is-torsorial-htpy-hom-Directed-Graph H G f)

  equiv-eq-total-hom-Directed-Graph :
    {l3 l4 : Level}
    (f g : Σ (Directed-Graph l3 l4) (λ H → hom-Directed-Graph H G)) →
    (f ＝ g) → equiv-total-hom-Directed-Graph f g
  equiv-eq-total-hom-Directed-Graph f .f refl =
    id-equiv-total-hom-Directed-Graph f

  is-equiv-equiv-eq-total-hom-Directed-Graph :
    {l3 l4 : Level}
    (f g : Σ (Directed-Graph l3 l4) (λ H → hom-Directed-Graph H G)) →
    is-equiv (equiv-eq-total-hom-Directed-Graph f g)
  is-equiv-equiv-eq-total-hom-Directed-Graph f =
    fundamental-theorem-id
      ( is-torsorial-equiv-total-hom-Directed-Graph f)
      ( equiv-eq-total-hom-Directed-Graph f)

  extensionality-total-hom-Directed-Graph :
    {l3 l4 : Level}
    (f g : Σ (Directed-Graph l3 l4) (λ H → hom-Directed-Graph H G)) →
    (f ＝ g) ≃ equiv-total-hom-Directed-Graph f g
  pr1 (extensionality-total-hom-Directed-Graph f g) =
    equiv-eq-total-hom-Directed-Graph f g
  pr2 (extensionality-total-hom-Directed-Graph f g) =
    is-equiv-equiv-eq-total-hom-Directed-Graph f g

  eq-equiv-total-hom-Directed-Graph :
    {l3 l4 : Level}
    (f g : Σ (Directed-Graph l3 l4) (λ H → hom-Directed-Graph H G)) →
    equiv-total-hom-Directed-Graph f g → f ＝ g
  eq-equiv-total-hom-Directed-Graph f g =
    map-inv-equiv (extensionality-total-hom-Directed-Graph f g)
```

#### The inverse map of the duality theorem is a retraction

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (G : Directed-Graph l1 l2)
  where

  is-retraction-map-inv-duality-Directed-Graph :
    is-retraction
      ( map-duality-Directed-Graph G {l1 ⊔ l3} {l2 ⊔ l4})
      ( map-inv-duality-Directed-Graph G {l1 ⊔ l3} {l2 ⊔ l4})
  is-retraction-map-inv-duality-Directed-Graph (H , f) =
    inv
      ( eq-equiv-total-hom-Directed-Graph G
        ( H , f)
        ( map-inv-duality-Directed-Graph G
          ( map-duality-Directed-Graph G (H , f)))
        ( ( compute-Σ-fiber-hom-Directed-Graph H G f) ,
          ( htpy-compute-Σ-fiber-hom-Directed-Graph H G f)))
```

#### The inverse map of the duality theorem is a section

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (G : Directed-Graph l1 l2)
  where

  is-section-map-inv-duality-Directed-Graph :
    is-section
      ( map-duality-Directed-Graph G {l1 ⊔ l3} {l2 ⊔ l4})
      ( map-inv-duality-Directed-Graph G {l1 ⊔ l3} {l2 ⊔ l4})
  is-section-map-inv-duality-Directed-Graph H =
    eq-equiv-Dependent-Directed-Graph
      ( fiber-pr1-Σ-Directed-Graph H)
      ( H)
      ( compute-fiber-pr1-Σ-Directed-Graph H)
```

#### The conclusion of the duality theorem

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (G : Directed-Graph l1 l2)
  where

  is-equiv-map-duality-Directed-Graph :
    is-equiv (map-duality-Directed-Graph G {l1 ⊔ l3} {l2 ⊔ l4})
  is-equiv-map-duality-Directed-Graph =
    is-equiv-is-invertible
      ( map-inv-duality-Directed-Graph G)
      ( is-section-map-inv-duality-Directed-Graph l3 l4 G)
      ( is-retraction-map-inv-duality-Directed-Graph l3 l4 G)

  duality-Directed-Graph :
    Σ (Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4)) (λ H → hom-Directed-Graph H G) ≃
    Dependent-Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4) G
  pr1 duality-Directed-Graph = map-duality-Directed-Graph G
  pr2 duality-Directed-Graph = is-equiv-map-duality-Directed-Graph
```
