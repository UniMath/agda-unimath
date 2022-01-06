---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module order-theory.finitely-graded-posets where

open import order-theory.posets public
```

## Finitely Graded Posets

The indexing number of a finitely graded poset is called its rank.

```agda

Finitely-Graded-Poset : (l1 l2 : Level) (k : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
Finitely-Graded-Poset l1 l2 k =
  Σ ( Fin (succ-ℕ k) → UU-Set l1)
    ( λ X →
      (i : Fin k) → type-Set (X (inl-Fin k i)) →
      type-Set (X (succ-Fin (inl-Fin k i))) → UU-Prop l2)

module _
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    (i : Fin (succ-ℕ k))
    where
    
    face-set-Finitely-Graded-Poset-Set : UU-Set l1
    face-set-Finitely-Graded-Poset-Set = pr1 X i

    face-set-Finitely-Graded-Poset : UU l1
    face-set-Finitely-Graded-Poset =
      type-Set face-set-Finitely-Graded-Poset-Set

    is-set-face-set-Finitely-Graded-Poset :
      is-set face-set-Finitely-Graded-Poset
    is-set-face-set-Finitely-Graded-Poset =
      is-set-type-Set face-set-Finitely-Graded-Poset-Set

  module _
    (i : Fin k) (y : face-set-Finitely-Graded-Poset (inl-Fin k i))
    (z : face-set-Finitely-Graded-Poset (succ-Fin (inl-Fin k i)))
    where

    adjacent-Finitely-Graded-Poset-Prop : UU-Prop l2
    adjacent-Finitely-Graded-Poset-Prop = pr2 X i y z
  
    adjacent-Finitely-Graded-Poset : UU l2
    adjacent-Finitely-Graded-Poset =
      type-Prop adjacent-Finitely-Graded-Poset-Prop

    is-prop-adjacent-Finitely-Graded-Poset :
      is-prop adjacent-Finitely-Graded-Poset
    is-prop-adjacent-Finitely-Graded-Poset =
      is-prop-type-Prop adjacent-Finitely-Graded-Poset-Prop    

  vertex-Finitely-Graded-Poset : UU l1
  vertex-Finitely-Graded-Poset =
    Σ (Fin (succ-ℕ k)) face-set-Finitely-Graded-Poset

  vertex-face-Finitely-Graded-Poset :
    {i : Fin (succ-ℕ k)} → face-set-Finitely-Graded-Poset i →
    vertex-Finitely-Graded-Poset
  vertex-face-Finitely-Graded-Poset {i} x = pair i x

  type-vertex-Finitely-Graded-Poset :
    vertex-Finitely-Graded-Poset → Fin (succ-ℕ k)
  type-vertex-Finitely-Graded-Poset (pair i x) = i

  face-vertex-Finitely-Graded-Poset :
    (x : vertex-Finitely-Graded-Poset) →
    face-set-Finitely-Graded-Poset (type-vertex-Finitely-Graded-Poset x)
  face-vertex-Finitely-Graded-Poset (pair i x) = x

  module _
    (x : vertex-Finitely-Graded-Poset)
    where

    data
      leq-Finitely-Graded-Poset :
        (y : vertex-Finitely-Graded-Poset) → UU (l1 ⊔ l2)
        where
        refl-leq-Finitely-Graded-Poset   :
          leq-Finitely-Graded-Poset x
        cons-leq-Finitely-Graded-Poset :
          {i : Fin k} (y : face-set-Finitely-Graded-Poset (inl-Fin k i))
          (z : face-set-Finitely-Graded-Poset (succ-Fin (inl-Fin k i))) →
          adjacent-Finitely-Graded-Poset i y z →
          leq-Finitely-Graded-Poset (vertex-face-Finitely-Graded-Poset y) →
          leq-Finitely-Graded-Poset (vertex-face-Finitely-Graded-Poset z)

{-
    all-elements-equal-leq-Finitely-Graded-Poset :
      (y : vertex-Finitely-Graded-Poset) →
      all-elements-equal (leq-Finitely-Graded-Poset y)
    all-elements-equal-leq-Finitely-Graded-Poset .x
      refl-leq-Finitely-Graded-Poset K = {!K!}
    all-elements-equal-leq-Finitely-Graded-Poset .(vertex-face-Finitely-Graded-Poset z) (cons-leq-Finitely-Graded-Poset y z x H) K = {!!}
-}

  transitive-leq-Finitely-Graded-Poset :
    (x y z : vertex-Finitely-Graded-Poset) →
    leq-Finitely-Graded-Poset y z → leq-Finitely-Graded-Poset x y →
    leq-Finitely-Graded-Poset x z
  transitive-leq-Finitely-Graded-Poset x y .y refl-leq-Finitely-Graded-Poset K =
    K
  transitive-leq-Finitely-Graded-Poset x y
    .(pair (succ-Fin (inl-Fin k _)) z)
    (cons-leq-Finitely-Graded-Poset w z v H) K =
    cons-leq-Finitely-Graded-Poset w z v
      ( transitive-leq-Finitely-Graded-Poset x y
        ( vertex-face-Finitely-Graded-Poset w)
        ( H)
        ( K))
