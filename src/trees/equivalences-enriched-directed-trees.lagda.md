# Equivalences of enriched directed trees

```agda
module trees.equivalences-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import trees.enriched-directed-trees
open import trees.equivalences-directed-trees
```

</details>

## Definition

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
            ( ( equiv-Σ
                ( λ y →
                  edge-Enriched-Directed-Tree A B T y
                    ( node-equiv-Directed-Tree
                      ( directed-tree-Enriched-Directed-Tree A B S)
                      ( directed-tree-Enriched-Directed-Tree A B T)
                      ( e)
                      ( x)))
                ( equiv-node-equiv-Directed-Tree
                  ( directed-tree-Enriched-Directed-Tree A B S)
                  ( directed-tree-Enriched-Directed-Tree A B T)
                  ( e))
                ( λ y →
                  equiv-edge-equiv-Directed-Tree
                    ( directed-tree-Enriched-Directed-Tree A B S)
                    ( directed-tree-Enriched-Directed-Tree A B T)
                    ( e)
                    ( y)
                    ( x))) ∘e
              ( equiv-children-Enriched-Directed-Tree A B S x))
            ( ( equiv-children-Enriched-Directed-Tree A B T
                ( node-equiv-Directed-Tree
                  ( directed-tree-Enriched-Directed-Tree A B S)
                  ( directed-tree-Enriched-Directed-Tree A B T)
                  ( e)
                  ( x))) ∘e
              ( equiv-tr B (H x)))))
```
