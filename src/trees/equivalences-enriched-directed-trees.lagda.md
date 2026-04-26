# Equivalences of enriched directed trees

```agda
module trees.equivalences-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import trees.enriched-directed-trees
open import trees.equivalences-directed-trees
open import trees.morphisms-directed-trees
open import trees.morphisms-enriched-directed-trees
open import trees.rooted-morphisms-enriched-directed-trees
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguation="of enriched directed tree" Agda=equiv-Enriched-Directed-Tree}}
of `(A,B)`-[enriched directed trees](trees.enriched-directed-trees.md) from `S`
to `T` is a shape-preserving [equivalence](trees.equivalences-directed-trees.md)
between their underlying trees, which also preserves the enrichment
equivalences.

## Definition

### The condition of being an equivalence of enriched directed trees

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (S : Enriched-Directed-Tree l3 l4 A B)
  (T : Enriched-Directed-Tree l5 l6 A B)
  where

  is-equiv-hom-Enriched-Directed-Tree :
    hom-Enriched-Directed-Tree A B S T → UU (l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-equiv-hom-Enriched-Directed-Tree f =
    is-equiv-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( directed-tree-hom-Enriched-Directed-Tree A B S T f)

  preserves-root-is-equiv-node-hom-Enriched-Directed-Tree :
    ( f : hom-Enriched-Directed-Tree A B S T) →
    is-equiv
      ( node-hom-Enriched-Directed-Tree A B S T f) →
    preserves-root-hom-Enriched-Directed-Tree A B S T f
  preserves-root-is-equiv-node-hom-Enriched-Directed-Tree f =
    preserves-root-is-equiv-node-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( directed-tree-hom-Enriched-Directed-Tree A B S T f)
```

### Equivalences of enriched directed trees

```agda
equiv-Enriched-Directed-Tree :
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2) →
  Enriched-Directed-Tree l3 l4 A B → Enriched-Directed-Tree l5 l6 A B →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
equiv-Enriched-Directed-Tree A B S T =
  Σ ( equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T))
    ( λ e →
      Σ ( coherence-triangle-maps
          ( shape-Enriched-Directed-Tree A B S)
          ( shape-Enriched-Directed-Tree A B T)
          ( node-equiv-Directed-Tree
            ( directed-tree-Enriched-Directed-Tree A B S)
            ( directed-tree-Enriched-Directed-Tree A B T)
            ( e)))
        ( λ H →
          (x : node-Enriched-Directed-Tree A B S) →
          htpy-equiv
            ( ( equiv-direct-predecessor-equiv-Directed-Tree
                ( directed-tree-Enriched-Directed-Tree A B S)
                ( directed-tree-Enriched-Directed-Tree A B T)
                ( e)
                ( x)) ∘e
              ( enrichment-Enriched-Directed-Tree A B S x))
            ( ( enrichment-Enriched-Directed-Tree A B T
                ( node-equiv-Directed-Tree
                  ( directed-tree-Enriched-Directed-Tree A B S)
                  ( directed-tree-Enriched-Directed-Tree A B T)
                  ( e)
                  ( x))) ∘e
              ( equiv-tr B (H x)))))

equiv-is-equiv-hom-Enriched-Directed-Tree :
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (S : Enriched-Directed-Tree l3 l4 A B)
  (T : Enriched-Directed-Tree l5 l6 A B) →
  (f : hom-Enriched-Directed-Tree A B S T) →
  is-equiv-hom-Enriched-Directed-Tree A B S T f →
  equiv-Enriched-Directed-Tree A B S T
equiv-is-equiv-hom-Enriched-Directed-Tree A B S T f H =
  map-Σ-map-base
    ( equiv-is-equiv-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( directed-tree-hom-Enriched-Directed-Tree A B S T f))
    ( _)
    ( H ,
      shape-hom-Enriched-Directed-Tree A B S T f ,
      enrichment-hom-Enriched-Directed-Tree A B S T f)

module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (S : Enriched-Directed-Tree l3 l4 A B) (T : Enriched-Directed-Tree l5 l6 A B)
  (e : equiv-Enriched-Directed-Tree A B S T)
  where

  equiv-directed-tree-equiv-Enriched-Directed-Tree :
    equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
  equiv-directed-tree-equiv-Enriched-Directed-Tree = pr1 e

  node-equiv-equiv-Enriched-Directed-Trhee :
    node-Enriched-Directed-Tree A B S ≃ node-Enriched-Directed-Tree A B T
  node-equiv-equiv-Enriched-Directed-Trhee =
    node-equiv-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  node-equiv-Enriched-Directed-Tree :
    node-Enriched-Directed-Tree A B S → node-Enriched-Directed-Tree A B T
  node-equiv-Enriched-Directed-Tree =
    node-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  edge-equiv-equiv-Enriched-Directed-Trhee :
    (x y : node-Enriched-Directed-Tree A B S) →
    edge-Enriched-Directed-Tree A B S x y ≃
    edge-Enriched-Directed-Tree A B T
      ( node-equiv-Enriched-Directed-Tree x)
      ( node-equiv-Enriched-Directed-Tree y)
  edge-equiv-equiv-Enriched-Directed-Trhee =
    edge-equiv-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  edge-equiv-Enriched-Directed-Tree :
    {x y : node-Enriched-Directed-Tree A B S} →
    edge-Enriched-Directed-Tree A B S x y →
    edge-Enriched-Directed-Tree A B T
      ( node-equiv-Enriched-Directed-Tree x)
      ( node-equiv-Enriched-Directed-Tree y)
  edge-equiv-Enriched-Directed-Tree =
    edge-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  hom-directed-tree-equiv-Enriched-Directed-Tree :
    hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
  hom-directed-tree-equiv-Enriched-Directed-Tree =
    hom-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  equiv-direct-predecessor-equiv-Enriched-Directed-Tree :
    ( x : node-Enriched-Directed-Tree A B S) →
    Σ ( node-Enriched-Directed-Tree A B S)
      ( λ y → edge-Enriched-Directed-Tree A B S y x) ≃
    Σ ( node-Enriched-Directed-Tree A B T)
      ( λ y →
        edge-Enriched-Directed-Tree A B T y
          ( node-equiv-Enriched-Directed-Tree x))
  equiv-direct-predecessor-equiv-Enriched-Directed-Tree =
    equiv-direct-predecessor-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  direct-predecessor-equiv-Enriched-Directed-Tree :
    ( x : node-Enriched-Directed-Tree A B S) →
    Σ ( node-Enriched-Directed-Tree A B S)
      ( λ y → edge-Enriched-Directed-Tree A B S y x) →
    Σ ( node-Enriched-Directed-Tree A B T)
      ( λ y →
        edge-Enriched-Directed-Tree A B T y
          ( node-equiv-Enriched-Directed-Tree x))
  direct-predecessor-equiv-Enriched-Directed-Tree =
    direct-predecessor-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  shape-equiv-Enriched-Directed-Tree :
    ( shape-Enriched-Directed-Tree A B S) ~
    ( shape-Enriched-Directed-Tree A B T ∘ node-equiv-Enriched-Directed-Tree)
  shape-equiv-Enriched-Directed-Tree = pr1 (pr2 e)

  enrichment-equiv-Enriched-Directed-Tree :
    ( x : node-Enriched-Directed-Tree A B S) →
    ( ( direct-predecessor-equiv-Enriched-Directed-Tree x) ∘
      ( map-enrichment-Enriched-Directed-Tree A B S x)) ~
    ( ( map-enrichment-Enriched-Directed-Tree A B T
        ( node-equiv-Directed-Tree
          ( directed-tree-Enriched-Directed-Tree A B S)
          ( directed-tree-Enriched-Directed-Tree A B T)
          ( equiv-directed-tree-equiv-Enriched-Directed-Tree)
          ( x))) ∘
        ( tr B (shape-equiv-Enriched-Directed-Tree x)))
  enrichment-equiv-Enriched-Directed-Tree = pr2 (pr2 e)

  hom-equiv-Enriched-Directed-Tree :
    hom-Enriched-Directed-Tree A B S T
  pr1 hom-equiv-Enriched-Directed-Tree =
    hom-directed-tree-equiv-Enriched-Directed-Tree
  pr1 (pr2 hom-equiv-Enriched-Directed-Tree) =
    shape-equiv-Enriched-Directed-Tree
  pr2 (pr2 hom-equiv-Enriched-Directed-Tree) =
    enrichment-equiv-Enriched-Directed-Tree

  preserves-root-equiv-Enriched-Directed-Tree :
    preserves-root-hom-Enriched-Directed-Tree A B S T
      hom-equiv-Enriched-Directed-Tree
  preserves-root-equiv-Enriched-Directed-Tree =
    preserves-root-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  rooted-hom-equiv-Enriched-Directed-Tree :
    rooted-hom-Enriched-Directed-Tree A B S T
  pr1 rooted-hom-equiv-Enriched-Directed-Tree =
    hom-equiv-Enriched-Directed-Tree
  pr2 rooted-hom-equiv-Enriched-Directed-Tree =
    preserves-root-equiv-Enriched-Directed-Tree
```

### The identity equivalence of enriched directed trees

```agda
id-equiv-Enriched-Directed-Tree :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) →
  (T : Enriched-Directed-Tree l3 l4 A B) →
  equiv-Enriched-Directed-Tree A B T T
pr1 (id-equiv-Enriched-Directed-Tree A B T) =
  id-equiv-Directed-Tree (directed-tree-Enriched-Directed-Tree A B T)
pr1 (pr2 (id-equiv-Enriched-Directed-Tree A B T)) = refl-htpy
pr2 (pr2 (id-equiv-Enriched-Directed-Tree A B T)) x = refl-htpy
```

### Composition of equivalences of enriched directed trees

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level} (A : UU l1) (B : A → UU l2)
  (R : Enriched-Directed-Tree l3 l4 A B)
  (S : Enriched-Directed-Tree l5 l6 A B)
  (T : Enriched-Directed-Tree l7 l8 A B)
  (g : equiv-Enriched-Directed-Tree A B S T)
  (f : equiv-Enriched-Directed-Tree A B R S)
  where

  equiv-directed-tree-comp-equiv-Enriched-Directed-Tree :
    equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B R)
      ( directed-tree-Enriched-Directed-Tree A B T)
  equiv-directed-tree-comp-equiv-Enriched-Directed-Tree =
    comp-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B R)
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree A B S T g)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree A B R S f)

  node-equiv-comp-equiv-Enriched-Directed-Tree :
    node-Enriched-Directed-Tree A B R ≃
    node-Enriched-Directed-Tree A B T
  node-equiv-comp-equiv-Enriched-Directed-Tree =
    node-equiv-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B R)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Tree)

  node-comp-equiv-Enriched-Directed-Tree :
    node-Enriched-Directed-Tree A B R →
    node-Enriched-Directed-Tree A B T
  node-comp-equiv-Enriched-Directed-Tree =
    node-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B R)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Tree)

  edge-equiv-comp-equiv-Enriched-Directed-Tree :
    (x y : node-Enriched-Directed-Tree A B R) →
    edge-Enriched-Directed-Tree A B R x y ≃
    edge-Enriched-Directed-Tree A B T
      ( node-comp-equiv-Enriched-Directed-Tree x)
      ( node-comp-equiv-Enriched-Directed-Tree y)
  edge-equiv-comp-equiv-Enriched-Directed-Tree =
    edge-equiv-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B R)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Tree)

  edge-comp-equiv-Enriched-Directed-Tree :
    {x y : node-Enriched-Directed-Tree A B R} →
    edge-Enriched-Directed-Tree A B R x y →
    edge-Enriched-Directed-Tree A B T
      ( node-comp-equiv-Enriched-Directed-Tree x)
      ( node-comp-equiv-Enriched-Directed-Tree y)
  edge-comp-equiv-Enriched-Directed-Tree =
    edge-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B R)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Tree)

  equiv-direct-predecessor-comp-equiv-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B R) →
    direct-predecessor-Enriched-Directed-Tree A B R x ≃
    direct-predecessor-Enriched-Directed-Tree A B T
      ( node-comp-equiv-Enriched-Directed-Tree x)
  equiv-direct-predecessor-comp-equiv-Enriched-Directed-Tree =
    equiv-direct-predecessor-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B R)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Tree)

  direct-predecessor-comp-equiv-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B R) →
    direct-predecessor-Enriched-Directed-Tree A B R x →
    direct-predecessor-Enriched-Directed-Tree A B T
      ( node-comp-equiv-Enriched-Directed-Tree x)
  direct-predecessor-comp-equiv-Enriched-Directed-Tree =
    direct-predecessor-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B R)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-comp-equiv-Enriched-Directed-Tree)

  shape-comp-equiv-Enriched-Directed-Tree :
    ( shape-Enriched-Directed-Tree A B R) ~
    ( shape-Enriched-Directed-Tree A B T ∘
      node-comp-equiv-Enriched-Directed-Tree)
  shape-comp-equiv-Enriched-Directed-Tree =
    concat-coherence-triangle-maps
      ( shape-Enriched-Directed-Tree A B R)
      ( shape-Enriched-Directed-Tree A B S)
      ( shape-Enriched-Directed-Tree A B T)
      ( node-equiv-Enriched-Directed-Tree A B R S f)
      ( node-equiv-Enriched-Directed-Tree A B S T g)
      ( shape-equiv-Enriched-Directed-Tree A B R S f)
      ( shape-equiv-Enriched-Directed-Tree A B S T g)

  enrichment-comp-equiv-Enriched-Directed-Tree :
    ( x : node-Enriched-Directed-Tree A B R) →
    coherence-square-maps
      ( tr B (shape-comp-equiv-Enriched-Directed-Tree x))
      ( map-enrichment-Enriched-Directed-Tree A B R x)
      ( map-enrichment-Enriched-Directed-Tree A B T
        ( node-comp-equiv-Enriched-Directed-Tree x))
      ( direct-predecessor-comp-equiv-Enriched-Directed-Tree x)
  enrichment-comp-equiv-Enriched-Directed-Tree x =
    pasting-horizontal-up-to-htpy-coherence-square-maps
      ( tr B (shape-equiv-Enriched-Directed-Tree A B R S f x))
      ( tr B
        ( shape-equiv-Enriched-Directed-Tree A B S T g
          ( node-equiv-Enriched-Directed-Tree A B R S f x)))
      ( map-enrichment-Enriched-Directed-Tree A B R x)
      ( map-enrichment-Enriched-Directed-Tree A B S
        ( node-equiv-Enriched-Directed-Tree A B R S f x))
      ( map-enrichment-Enriched-Directed-Tree A B T
        ( node-comp-equiv-Enriched-Directed-Tree x))
      ( direct-predecessor-equiv-Enriched-Directed-Tree A B R S f x)
      ( direct-predecessor-equiv-Enriched-Directed-Tree A B S T g
        ( node-equiv-Enriched-Directed-Tree A B R S f x))
      ( tr-concat
        ( shape-equiv-Enriched-Directed-Tree A B R S f x)
        ( shape-equiv-Enriched-Directed-Tree A B S T g
          ( node-equiv-Enriched-Directed-Tree A B R S f x)))
      ( refl-htpy)
      ( enrichment-equiv-Enriched-Directed-Tree A B R S f x)
      ( enrichment-equiv-Enriched-Directed-Tree A B S T g
        ( node-equiv-Enriched-Directed-Tree A B R S f x))

  comp-equiv-Enriched-Directed-Tree :
    equiv-Enriched-Directed-Tree A B R T
  pr1 comp-equiv-Enriched-Directed-Tree =
    equiv-directed-tree-comp-equiv-Enriched-Directed-Tree
  pr1 (pr2 comp-equiv-Enriched-Directed-Tree) =
    shape-comp-equiv-Enriched-Directed-Tree
  pr2 (pr2 comp-equiv-Enriched-Directed-Tree) =
    enrichment-comp-equiv-Enriched-Directed-Tree
```

### Homotopies of equivalences of enriched directed trees

```agda
htpy-equiv-Enriched-Directed-Tree :
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2) →
  (S : Enriched-Directed-Tree l3 l4 A B) (T : Enriched-Directed-Tree l5 l6 A B)
  (e f : equiv-Enriched-Directed-Tree A B S T) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
htpy-equiv-Enriched-Directed-Tree A B S T e f =
  htpy-hom-Enriched-Directed-Tree A B S T
    ( hom-equiv-Enriched-Directed-Tree A B S T e)
    ( hom-equiv-Enriched-Directed-Tree A B S T f)
```

## Properties

### Equivalences characterize identifications of enriched directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  extensionality-Enriched-Directed-Tree :
    (S : Enriched-Directed-Tree l3 l4 A B) →
    (T ＝ S) ≃ equiv-Enriched-Directed-Tree A B T S
  extensionality-Enriched-Directed-Tree =
    extensionality-Σ
      ( λ {S} (sh , enr) e →
        Σ ( ( shape-Enriched-Directed-Tree A B T) ~
            ( ( sh) ∘
              ( node-equiv-Directed-Tree
                ( directed-tree-Enriched-Directed-Tree A B T)
                ( S)
                ( e))))
          ( λ H →
            ( x : node-Enriched-Directed-Tree A B T) →
            ( ( direct-predecessor-equiv-Directed-Tree
                ( directed-tree-Enriched-Directed-Tree A B T)
                ( S)
                ( e)
                ( x)) ∘
              ( map-enrichment-Enriched-Directed-Tree A B T x)) ~
            ( ( map-equiv
                ( enr
                  ( node-equiv-Directed-Tree
                    ( directed-tree-Enriched-Directed-Tree A B T)
                    ( S)
                    ( e)
                    ( x)))) ∘
              ( tr B (H x)))))
      ( id-equiv-Directed-Tree (directed-tree-Enriched-Directed-Tree A B T))
      ( ( refl-htpy) ,
        ( λ x → refl-htpy))
      ( extensionality-Directed-Tree
        ( directed-tree-Enriched-Directed-Tree A B T))
      ( extensionality-Σ
        ( λ {sh} enr H →
          ( x : node-Enriched-Directed-Tree A B T) →
          ( map-enrichment-Enriched-Directed-Tree A B T x) ~
          ( map-equiv (enr x) ∘ tr B (H x)))
        ( refl-htpy)
        ( λ x → refl-htpy)
        ( λ sh → equiv-funext)
        ( extensionality-Π
          ( enrichment-Enriched-Directed-Tree A B T)
          ( λ x e →
            ( map-enrichment-Enriched-Directed-Tree A B T x) ~
            ( map-equiv e))
          ( λ x →
            extensionality-equiv
            ( enrichment-Enriched-Directed-Tree A B T x))))

  equiv-eq-Enriched-Directed-Tree :
    (S : Enriched-Directed-Tree l3 l4 A B) →
    (T ＝ S) → equiv-Enriched-Directed-Tree A B T S
  equiv-eq-Enriched-Directed-Tree S =
    map-equiv (extensionality-Enriched-Directed-Tree S)

  eq-equiv-Enriched-Directed-Tree :
    (S : Enriched-Directed-Tree l3 l4 A B) →
    equiv-Enriched-Directed-Tree A B T S → T ＝ S
  eq-equiv-Enriched-Directed-Tree S =
    map-inv-equiv (extensionality-Enriched-Directed-Tree S)

  is-torsorial-equiv-Enriched-Directed-Tree :
    is-torsorial (equiv-Enriched-Directed-Tree A B T)
  is-torsorial-equiv-Enriched-Directed-Tree =
    is-contr-equiv'
      ( Σ (Enriched-Directed-Tree l3 l4 A B) (λ S → T ＝ S))
      ( equiv-tot extensionality-Enriched-Directed-Tree)
      ( is-torsorial-Id T)
```

### A morphism of enriched directed trees is an equivalence if it is an equivalence on the nodes

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (S : Enriched-Directed-Tree l3 l4 A B)
  (T : Enriched-Directed-Tree l5 l6 A B)
  (f : hom-Enriched-Directed-Tree A B S T)
  where

  is-equiv-is-equiv-node-hom-Enriched-Directed-Tree :
    is-equiv (node-hom-Enriched-Directed-Tree A B S T f) →
    is-equiv-hom-Enriched-Directed-Tree A B S T f
  is-equiv-is-equiv-node-hom-Enriched-Directed-Tree =
    is-equiv-is-equiv-node-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( directed-tree-hom-Enriched-Directed-Tree A B S T f)
```
