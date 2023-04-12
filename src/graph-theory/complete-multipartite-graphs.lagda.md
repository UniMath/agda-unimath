# Complete multipartite graphs

```agda
module graph-theory.complete-multipartite-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.finite-graphs

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
```

</details>

## Idea

A complete multipartite graph consists of a finite list of sets `V1,…,Vn`, and
for each unordered pair of distinct elements `i,j≤n` and each `x : Vi` and
`y : Vj` an edge between `x` and `y`.

```agda
complete-multipartite-Undirected-Graph-𝔽 :
  {l1 l2 : Level} (X : 𝔽 l1) (Y : type-𝔽 X → 𝔽 l2) →
  Undirected-Graph-𝔽 (l1 ⊔ l2) l1
pr1 (complete-multipartite-Undirected-Graph-𝔽 X Y) = Σ-𝔽 X Y
pr2 (complete-multipartite-Undirected-Graph-𝔽 X Y) p =
  ( Π-𝔽 ( finite-type-2-Element-Type (pr1 p))
        ( λ x →
          Π-𝔽 ( finite-type-2-Element-Type (pr1 p))
              ( λ y →
                Id-𝔽 X
                  ( pr1 (element-unordered-pair p x))
                  ( pr1 (element-unordered-pair p y))))) →-𝔽
  empty-𝔽
```
