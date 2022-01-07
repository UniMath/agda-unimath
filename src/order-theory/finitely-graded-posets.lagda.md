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

  sim-Finitely-Graded-Poset :
    (x y : vertex-Finitely-Graded-Poset) → UU (l1 ⊔ l2)
  sim-Finitely-Graded-Poset x y =
    leq-Finitely-Graded-Poset x y × leq-Finitely-Graded-Poset y x

  refl-sim-Finitely-Graded-Poset :
    (x : vertex-Finitely-Graded-Poset) → sim-Finitely-Graded-Poset x x
  pr1 (refl-sim-Finitely-Graded-Poset x) = refl-leq-Finitely-Graded-Poset
  pr2 (refl-sim-Finitely-Graded-Poset x) = refl-leq-Finitely-Graded-Poset

  sim-eq-Finitely-Graded-Poset :
    (x y : vertex-Finitely-Graded-Poset) →
    Id x y → sim-Finitely-Graded-Poset x y
  sim-eq-Finitely-Graded-Poset x .x refl = refl-sim-Finitely-Graded-Poset x
```

### Truncating finitely graded posets

```agda

module _
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 (succ-ℕ k))
  where
  
  trunc-Finitely-Graded-Poset : Finitely-Graded-Poset l1 l2 k
  pr1 trunc-Finitely-Graded-Poset i =
    face-set-Finitely-Graded-Poset-Set (succ-ℕ k) X (inl-Fin (succ-ℕ k) i)
  pr2 trunc-Finitely-Graded-Poset i =
    adjacent-Finitely-Graded-Poset-Prop (succ-ℕ k) X (inl-Fin k i)

  vertex-trunc-Finitely-Graded-Poset : UU l1
  vertex-trunc-Finitely-Graded-Poset =
    vertex-Finitely-Graded-Poset k trunc-Finitely-Graded-Poset

  leq-trunc-Finitely-Graded-Poset :
    (x y : vertex-trunc-Finitely-Graded-Poset) → UU (l1 ⊔ l2)
  leq-trunc-Finitely-Graded-Poset =
    leq-Finitely-Graded-Poset k trunc-Finitely-Graded-Poset

  vertex-vertex-trunc-Finitely-Graded-Poset :
    vertex-trunc-Finitely-Graded-Poset →
    vertex-Finitely-Graded-Poset (succ-ℕ k) X
  pr1 (vertex-vertex-trunc-Finitely-Graded-Poset (pair i x)) =
    inl-Fin (succ-ℕ k) i
  pr2 (vertex-vertex-trunc-Finitely-Graded-Poset (pair i x)) = x
```

### Antisymmetry of finitely graded posets

```agda
center-total-leq-Finitely-Graded-Poset :
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k)
  (i : Fin (succ-ℕ k)) (x : face-set-Finitely-Graded-Poset k X i) →
  Σ ( vertex-Finitely-Graded-Poset k X)
    ( λ y →
      Id (type-vertex-Finitely-Graded-Poset k X y) i ×
      leq-Finitely-Graded-Poset k X
        ( vertex-face-Finitely-Graded-Poset k X x)
        y)
pr1 (center-total-leq-Finitely-Graded-Poset k X i x) =
  vertex-face-Finitely-Graded-Poset k X x
pr1 (pr2 (center-total-leq-Finitely-Graded-Poset k X i x)) = refl
pr2 (pr2 (center-total-leq-Finitely-Graded-Poset k X i x)) =
  refl-leq-Finitely-Graded-Poset

contraction-total-leq-Finitely-Graded-Poset :
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k)
  (i : Fin (succ-ℕ k)) (x : face-set-Finitely-Graded-Poset k X i) →
  ( p : Σ ( vertex-Finitely-Graded-Poset k X)
          ( λ y →
            Id (type-vertex-Finitely-Graded-Poset k X y) i ×
            leq-Finitely-Graded-Poset k X
              ( vertex-face-Finitely-Graded-Poset k X x)
              ( y))) →
  Id (center-total-leq-Finitely-Graded-Poset k X i x) p
contraction-total-leq-Finitely-Graded-Poset zero-ℕ X (inr star) x
  ( pair (pair .(inr star) .x) (pair p refl-leq-Finitely-Graded-Poset)) =
  ap
    ( pair (vertex-face-Finitely-Graded-Poset zero-ℕ X x))
    ( ap
      ( λ t → pair t refl-leq-Finitely-Graded-Poset)
      ( eq-is-prop (is-set-Fin one-ℕ (inr star) (inr star))))
contraction-total-leq-Finitely-Graded-Poset (succ-ℕ k) X i x (pair y H) = {!!}

-- is-contr-total-leq-Finitely-Graded-Poset :
--   {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k)
--   (i : Fin (succ-ℕ k)) (x : face-set-Finitely-Graded-Poset k X i) →
--   is-contr
--     ( Σ ( face-set-Finitely-Graded-Poset k X i)
--         ( λ y →
--           leq-Finitely-Graded-Poset k X
--             ( vertex-face-Finitely-Graded-Poset k X x)
--             ( vertex-face-Finitely-Graded-Poset k X y)))
-- is-contr-total-leq-Finitely-Graded-Poset k X i x = {!!}

-- contraction-total-sim-Finitely-Graded-Poset :
--   {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k)
--   (x : vertex-Finitely-Graded-Poset k X) →
--   (p : Σ (vertex-Finitely-Graded-Poset k X) (sim-Finitely-Graded-Poset k X x)) →
--   Id (pair x (refl-sim-Finitely-Graded-Poset k X x)) p
-- contraction-total-sim-Finitely-Graded-Poset zero-ℕ X (pair i x) (pair (pair .i .x) (pair refl-leq-Finitely-Graded-Poset K)) = {!!}
-- contraction-total-sim-Finitely-Graded-Poset (succ-ℕ k) X x (pair y H) = {!!}

-- is-contr-total-sim-Finitely-Graded-Poset :
--   {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k)
--   (x : vertex-Finitely-Graded-Poset k X) →
--   is-contr
--     ( Σ ( vertex-Finitely-Graded-Poset k X) ( sim-Finitely-Graded-Poset k X x))
-- is-contr-total-sim-Finitely-Graded-Poset k X x =
--   {!!}
