# Equivalences of enriched directed trees

```agda
module trees.equivalences-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import trees.enriched-directed-trees
open import trees.equivalences-directed-trees
open import trees.morphisms-directed-trees
open import trees.morphisms-enriched-directed-trees
```

</details>

## Definition

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
      Σ ( ( shape-Enriched-Directed-Tree A B S) ~
          ( ( shape-Enriched-Directed-Tree A B T) ∘
            ( node-equiv-Directed-Tree
              ( directed-tree-Enriched-Directed-Tree A B S)
              ( directed-tree-Enriched-Directed-Tree A B T)
              ( e))))
        ( λ H →
          (x : node-Enriched-Directed-Tree A B S) →
          htpy-equiv
            ( ( equiv-children-equiv-Directed-Tree
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

  equiv-node-equiv-Enriched-Directed-Tree :
    node-Enriched-Directed-Tree A B S ≃ node-Enriched-Directed-Tree A B T
  equiv-node-equiv-Enriched-Directed-Tree =
    equiv-node-equiv-Directed-Tree
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

  equiv-edge-equiv-Enriched-Directed-Tree :
    (x y : node-Enriched-Directed-Tree A B S) →
    edge-Enriched-Directed-Tree A B S x y ≃
    edge-Enriched-Directed-Tree A B T
      ( node-equiv-Enriched-Directed-Tree x)
      ( node-equiv-Enriched-Directed-Tree y)
  equiv-edge-equiv-Enriched-Directed-Tree =
    equiv-edge-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  edge-equiv-Enriched-Directed-Tree :
    (x y : node-Enriched-Directed-Tree A B S) →
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

  equiv-children-equiv-Enriched-Directed-Tree :
    ( x : node-Enriched-Directed-Tree A B S) →
    Σ ( node-Enriched-Directed-Tree A B S)
      ( λ y → edge-Enriched-Directed-Tree A B S y x) ≃
    Σ ( node-Enriched-Directed-Tree A B T)
      ( λ y →
        edge-Enriched-Directed-Tree A B T y
          ( node-equiv-Enriched-Directed-Tree x))
  equiv-children-equiv-Enriched-Directed-Tree =
    equiv-children-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  children-equiv-Enriched-Directed-Tree :
    ( x : node-Enriched-Directed-Tree A B S) →
    Σ ( node-Enriched-Directed-Tree A B S)
      ( λ y → edge-Enriched-Directed-Tree A B S y x) →
    Σ ( node-Enriched-Directed-Tree A B T)
      ( λ y →
        edge-Enriched-Directed-Tree A B T y
          ( node-equiv-Enriched-Directed-Tree x))
  children-equiv-Enriched-Directed-Tree =
    children-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)

  shape-equiv-Enriched-Directed-Tree :
    ( shape-Enriched-Directed-Tree A B S) ~
    ( shape-Enriched-Directed-Tree A B T ∘ node-equiv-Enriched-Directed-Tree)
  shape-equiv-Enriched-Directed-Tree = pr1 (pr2 e)

  enrichment-equiv-Enriched-Directed-Tree :
    ( x : node-Enriched-Directed-Tree A B S) →
    ( ( children-equiv-Enriched-Directed-Tree x) ∘
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
    node-equiv-Enriched-Directed-Tree (root-Enriched-Directed-Tree A B S) ＝
    root-Enriched-Directed-Tree A B T
  preserves-root-equiv-Enriched-Directed-Tree =
    preserves-root-equiv-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( equiv-directed-tree-equiv-Enriched-Directed-Tree)
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
            ( ( children-equiv-Directed-Tree
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

  is-contr-total-equiv-Enriched-Directed-Tree :
    is-contr
      ( Σ ( Enriched-Directed-Tree l3 l4 A B)
          ( equiv-Enriched-Directed-Tree A B T))
  is-contr-total-equiv-Enriched-Directed-Tree =
    is-contr-equiv'
      ( Σ (Enriched-Directed-Tree l3 l4 A B) (λ S → T ＝ S))
      ( equiv-tot extensionality-Enriched-Directed-Tree)
      ( is-contr-total-path T)
```
