# Complete bipartite graphs

```agda
module graph-theory.complete-bipartite-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.finite-graphs

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.fibers-of-maps
open import univalent-combinatorics.finite-types
```

</details>

## Definition

```agda
complete-bipartite-Undirected-Graph-𝔽 :
  {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → Undirected-Graph-𝔽 (l1 ⊔ l2) (l1 ⊔ l2)
pr1 (complete-bipartite-Undirected-Graph-𝔽 X Y) = coprod-𝔽 X Y
pr2 (complete-bipartite-Undirected-Graph-𝔽 X Y) p =
  prod-𝔽 ( Σ-𝔽 X
           ( λ x →
             fib-𝔽
               ( finite-type-2-Element-Type (pr1 p))
               ( coprod-𝔽 X Y)
               ( element-unordered-pair p)
               ( inl x)))
         ( Σ-𝔽 Y
           ( λ y →
             fib-𝔽
               ( finite-type-2-Element-Type (pr1 p))
               ( coprod-𝔽 X Y)
               ( element-unordered-pair p)
               ( inr y)))
```
