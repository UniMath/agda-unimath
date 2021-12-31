---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.finite-graphs where

open import univalent-combinatorics.unordered-pairs public

record Graph-Fin : UU (lsuc lzero)
  where
  field
    V : ℕ
    E : (unordered-pair (Fin V)) → ℕ

record Graph-Fin' : UU (lsuc lzero)
  where
  field
    V : ℕ
    E : Fin V → Fin V → ℕ
    σ : (x y : Fin V) → Id (E x y) (E y x)

record Graph-𝔽 : UU (lsuc lzero)
  where
  field
    vertex : 𝔽
    edge : unordered-pair (type-𝔽 vertex) → 𝔽

vertices-Graph-𝔽 : (G : Graph-𝔽) → UU lzero
vertices-Graph-𝔽 G = type-𝔽 (Graph-𝔽.vertex G)

is-finite-vertices-Graph-𝔽 : (G : Graph-𝔽) → is-finite (vertices-Graph-𝔽 G)
is-finite-vertices-Graph-𝔽 G = is-finite-type-𝔽 (Graph-𝔽.vertex G)

edges-Graph-𝔽 :
  (G : Graph-𝔽) (p : unordered-pair (vertices-Graph-𝔽 G)) → UU lzero
edges-Graph-𝔽 G p = type-𝔽 (Graph-𝔽.edge G p)

is-finite-edges-Graph-𝔽 :
  (G : Graph-𝔽) (p : unordered-pair (vertices-Graph-𝔽 G)) →
  is-finite (edges-Graph-𝔽 G p)
is-finite-edges-Graph-𝔽 G p = is-finite-type-𝔽 (Graph-𝔽.edge G p)

total-edges-Graph-𝔽 : (G : Graph-𝔽) → UU (lsuc lzero)
total-edges-Graph-𝔽 G =
  Σ (unordered-pair (vertices-Graph-𝔽 G)) (edges-Graph-𝔽 G)

{- The type total-edges-Graph-𝔽 isn't expected to be finite, but its set
   truncation should be. -}

{- The following type is expected to be equivalent to Graph-𝔽 -}

record Graph-𝔽' : UU (lsuc lzero)
  where
  field
    vertex : 𝔽
    edge : type-𝔽 vertex → type-𝔽 vertex → 𝔽
    σ : (x y : type-𝔽 vertex) → type-𝔽 (edge x y) ≃ type-𝔽 (edge y x)
    σ² : (x y : type-𝔽 vertex) → map-equiv ((σ y x) ∘e (σ x y)) ~ id
  
{- The degree of a vertex x of a graph G is the set of occurences of x as an
   endpoint of x. Note that the unordered pair {x,x} adds two elements to the 
   degree of x.  -}

incident-edges-vertex-Graph-𝔽 :
  (G : Graph-𝔽) (x : type-𝔽 (Graph-𝔽.vertex G)) → UU (lsuc lzero)
incident-edges-vertex-Graph-𝔽 G x =
  Σ ( unordered-pair (type-𝔽 (Graph-𝔽.vertex G)))
    ( λ p → fib (element-unordered-pair p) x)

{-
neighbor-Graph-𝔽 :
  (G : Graph-𝔽) (x : vertices-Graph-𝔽 G) → UU (lsuc lzero)
neighbor-Graph-𝔽 G x = Σ (vertices-Graph-𝔽 G) (λ y → type-trunc-Prop {!!})
-}

--------------------------------------------------------------------------------

{- We formalize the definitions of complete multipartite graphs, complete
   graphs, and complete bipartite graphs. -}

two-element-type-𝔽 : UU-Fin two-ℕ → 𝔽
two-element-type-𝔽 X =
  pair (pr1 X) (is-finite-has-finite-cardinality (pair two-ℕ (pr2 X)))

complete-multipartite-Graph-𝔽 : (X : 𝔽) (Y : type-𝔽 X → 𝔽) → Graph-𝔽
Graph-𝔽.vertex (complete-multipartite-Graph-𝔽 X Y) = Σ-𝔽 X Y
Graph-𝔽.edge (complete-multipartite-Graph-𝔽 X Y) p =
  ( Π-𝔽 ( two-element-type-𝔽 (pr1 p))
        ( λ x →
          Π-𝔽 ( two-element-type-𝔽 (pr1 p))
              ( λ y →
                Id-𝔽 X
                  ( pr1 (element-unordered-pair p x))
                  ( pr1 (element-unordered-pair p y))))) →-𝔽
  empty-𝔽

complete-Graph-𝔽 : 𝔽 → Graph-𝔽
complete-Graph-𝔽 X = complete-multipartite-Graph-𝔽 X (λ x → unit-𝔽)

complete-bipartite-Graph-𝔽 : 𝔽 → 𝔽 → Graph-𝔽
Graph-𝔽.vertex (complete-bipartite-Graph-𝔽 X Y) = coprod-𝔽 X Y
Graph-𝔽.edge (complete-bipartite-Graph-𝔽 X Y) p =
  prod-𝔽 ( Σ-𝔽 X
           ( λ x →
             fib-𝔽
               ( two-element-type-𝔽 (pr1 p))
               ( coprod-𝔽 X Y)
               ( element-unordered-pair p)
               ( inl x)))
         ( Σ-𝔽 Y
           ( λ y →
             fib-𝔽
               ( two-element-type-𝔽 (pr1 p))
               ( coprod-𝔽 X Y)
               ( element-unordered-pair p)
               ( inr y)))
```
