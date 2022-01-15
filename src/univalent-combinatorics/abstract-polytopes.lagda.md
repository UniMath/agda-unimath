---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.abstract-polytopes where

open import order-theory public
```

## Axiom P1 of polytopes

The first axiom of polytopes asserts that polytopes have a least and a largest element.

```agda

module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  P1-Polytope-Prop : UU-Prop (l1 ⊔ l2)
  P1-Polytope-Prop =
    prod-Prop
      ( least-element-Finitely-Graded-Poset-Prop X)
      ( largest-element-Finitely-Graded-Poset-Prop X)

  P1-Polytope : UU (l1 ⊔ l2)
  P1-Polytope = type-Prop P1-Polytope-Prop

  is-prop-P1-Polytope : is-prop P1-Polytope
  is-prop-P1-Polytope = is-prop-type-Prop P1-Polytope-Prop
```

## Axiom P2 of polytopes

The second axiom of polytopes asserts that every maximal chain has k elements. Here, the natural number k is the rank of the polytope. In classical mathematics, this axiom implies that the underlying poset of a polytope is graded. Here, we will assume that polytopes come equipped with a grading.

  (P2') The poset X is graded, and the maximal chains in X have exactly (k + 1) elements.

```agda
module _
  {l1 l2 : Level} (l3 : Level) {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where  
  
  P2-Polytope-Prop : UU-Prop (l1 ⊔ l2 ⊔ lsuc l3)
  P2-Polytope-Prop =
    Π-Prop
      ( maximal-chain-Poset l3 (poset-Finitely-Graded-Poset X))
      ( λ C →
        has-cardinality-Prop
          ( element-maximal-chain-Poset (poset-Finitely-Graded-Poset X) C)
          ( succ-ℕ k))

  P2-Polytope : UU (l1 ⊔ l2 ⊔ lsuc l3)
  P2-Polytope = type-Prop P2-Polytope-Prop

  is-prop-P2-Polytope : is-prop P2-Polytope
  is-prop-P2-Polytope = is-prop-type-Prop P2-Polytope-Prop

Prepolytope : (l1 l2 l3 : Level) → ℕ → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Prepolytope l1 l2 l3 k =
  Σ ( Finitely-Graded-Poset l1 l2 k)
    ( λ X → P1-Polytope X × P2-Polytope l3 X)

module _
  {l1 l2 l3 : Level} (k : ℕ) (X : Prepolytope l1 l2 l3 k)
  where

  finitely-graded-poset-Prepolytope : Finitely-Graded-Poset l1 l2 k
  finitely-graded-poset-Prepolytope = pr1 X

  P1-polytope-Prepolytope : P1-Polytope finitely-graded-poset-Prepolytope
  P1-polytope-Prepolytope = pr1 (pr2 X)

  P2-polytope-Prepolytope : P2-Polytope l3 finitely-graded-poset-Prepolytope
  P2-polytope-Prepolytope = pr2 (pr2 X)

  module _
    (i : Fin (succ-ℕ k))
    where

    face-set-Prepolytope : UU-Set l1
    face-set-Prepolytope =
      face-set-Finitely-Graded-Poset finitely-graded-poset-Prepolytope i

    face-Prepolytope : UU l1
    face-Prepolytope =
      face-Finitely-Graded-Poset finitely-graded-poset-Prepolytope i

    is-set-face-Prepolytope : is-set face-Prepolytope
    is-set-face-Prepolytope =
      is-set-face-Finitely-Graded-Poset finitely-graded-poset-Prepolytope i

  module _
    (i : Fin k) (y : face-Prepolytope (inl-Fin k i))
    (z : face-Prepolytope (succ-Fin (inl-Fin k i)))
    where

    adjacent-Prepolytope-Prop : UU-Prop l2
    adjacent-Prepolytope-Prop =
      adjacent-Finitely-Graded-Poset-Prop
        ( finitely-graded-poset-Prepolytope)
        ( i)
        ( y)
        ( z)

    adjacent-Prepolytope : UU l2
    adjacent-Prepolytope =
      adjacent-Finitely-Graded-Poset finitely-graded-poset-Prepolytope i y z

    is-prop-adjacent-Prepolytope : is-prop adjacent-Prepolytope
    is-prop-adjacent-Prepolytope =
      is-prop-adjacent-Finitely-Graded-Poset
        ( finitely-graded-poset-Prepolytope)
        ( i)
        ( y)
        ( z)

  element-set-Prepolytope : UU-Set l1
  element-set-Prepolytope =
    element-set-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  element-Prepolytope : UU l1
  element-Prepolytope =
    element-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  is-set-element-Prepolytope : is-set element-Prepolytope
  is-set-element-Prepolytope =
    is-set-element-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  element-face-Prepolytope :
    {i : Fin (succ-ℕ k)} → face-Prepolytope i → element-Prepolytope
  element-face-Prepolytope =
    element-face-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

--------------------------------------------------------------------------------
    
{-
  type-element-Finitely-Graded-Poset :
    element-Finitely-Graded-Poset → Fin (succ-ℕ k)
  type-element-Finitely-Graded-Poset (pair i x) = i

  face-element-Finitely-Graded-Poset :
    (x : element-Finitely-Graded-Poset) →
    face-Finitely-Graded-Poset (type-element-Finitely-Graded-Poset x)
  face-element-Finitely-Graded-Poset (pair i x) = x

  module _
    {i : Fin (succ-ℕ k)} (x : face-Finitely-Graded-Poset i)
    where

    {- If chains with jumps are never used, we'd like to call the following
       chains. -}

    data
      path-faces-Finitely-Graded-Poset :
        {j : Fin (succ-ℕ k)} (y : face-Finitely-Graded-Poset j) →
        UU (l1 ⊔ l2)
        where
        refl-path-faces-Finitely-Graded-Poset :
          path-faces-Finitely-Graded-Poset x
        cons-path-faces-Finitely-Graded-Poset :
          {j : Fin k} {y : face-Finitely-Graded-Poset (inl-Fin k j)}
          {z : face-Finitely-Graded-Poset (succ-Fin (inl-Fin k j))} →
          adjacent-Finitely-Graded-Poset j y z →
          path-faces-Finitely-Graded-Poset y →
          path-faces-Finitely-Graded-Poset z

  tr-refl-path-faces-Finitely-Graded-Poset :
    {i j : Fin (succ-ℕ k)} (p : Id j i) (x : face-Finitely-Graded-Poset j) →
    path-faces-Finitely-Graded-Poset
      ( tr face-Finitely-Graded-Poset p x)
      ( x)
  tr-refl-path-faces-Finitely-Graded-Poset refl x =
    refl-path-faces-Finitely-Graded-Poset

  concat-path-faces-Finitely-Graded-Poset :
    {i1 i2 i3 : Fin (succ-ℕ k)}
    {x : face-Finitely-Graded-Poset i1}
    {y : face-Finitely-Graded-Poset i2}
    {z : face-Finitely-Graded-Poset i3} →
    path-faces-Finitely-Graded-Poset y z →
    path-faces-Finitely-Graded-Poset x y →
    path-faces-Finitely-Graded-Poset x z
  concat-path-faces-Finitely-Graded-Poset
    refl-path-faces-Finitely-Graded-Poset K = K
  concat-path-faces-Finitely-Graded-Poset
    ( cons-path-faces-Finitely-Graded-Poset x H) K =
    cons-path-faces-Finitely-Graded-Poset x
      ( concat-path-faces-Finitely-Graded-Poset H K)

  path-vertices-Finitely-Graded-Poset :
    (x y : element-Finitely-Graded-Poset) → UU (l1 ⊔ l2)
  path-vertices-Finitely-Graded-Poset (pair i x) (pair j y) =
    path-faces-Finitely-Graded-Poset x y

  refl-path-vertices-Finitely-Graded-Poset :
    (x : element-Finitely-Graded-Poset) → path-vertices-Finitely-Graded-Poset x x
  refl-path-vertices-Finitely-Graded-Poset x =
    refl-path-faces-Finitely-Graded-Poset

  concat-path-vertices-Finitely-Graded-Poset :
    (x y z : element-Finitely-Graded-Poset) →
    path-vertices-Finitely-Graded-Poset y z →
    path-vertices-Finitely-Graded-Poset x y →
    path-vertices-Finitely-Graded-Poset x z
  concat-path-vertices-Finitely-Graded-Poset x y z =
    concat-path-faces-Finitely-Graded-Poset

  leq-type-path-faces-Finitely-Graded-Poset :
    {i1 i2 : Fin (succ-ℕ k)} (x : face-Finitely-Graded-Poset i1)
    (y : face-Finitely-Graded-Poset i2) →
    path-faces-Finitely-Graded-Poset x y → leq-Fin i1 i2
  leq-type-path-faces-Finitely-Graded-Poset {i1} x .x
    refl-path-faces-Finitely-Graded-Poset = refl-leq-Fin i1
  leq-type-path-faces-Finitely-Graded-Poset {i1} x y
    ( cons-path-faces-Finitely-Graded-Poset {i3} {z} H K) =
    transitive-leq-Fin {succ-ℕ k} {i1}
      ( leq-type-path-faces-Finitely-Graded-Poset x z K)
      ( leq-succ-Fin i3)
      -}


```

  (P4) We state the diamond condition

```agda

diamond-condition-Finitely-Graded-Poset :
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k) →
  UU-Prop (l1 ⊔ l2)
diamond-condition-Finitely-Graded-Poset zero-ℕ X = raise-unit-Prop _
diamond-condition-Finitely-Graded-Poset (succ-ℕ k) X =
  Π-Prop
    ( Fin k)
    ( λ i →
      Π-Prop
        ( face-Finitely-Graded-Poset X (inl-Fin (succ-ℕ k) (inl-Fin k i)))
        ( λ x →
          Π-Prop
            ( face-Finitely-Graded-Poset X
              ( succ-Fin (succ-Fin (inl-Fin (succ-ℕ k) (inl-Fin k i)))))
            ( λ y →
              has-cardinality-Prop
                ( Σ ( face-Finitely-Graded-Poset X
                      ( succ-Fin (inl-Fin (succ-ℕ k) (inl-Fin k i))))
                    ( λ z →
                      adjacent-Finitely-Graded-Poset X (inl-Fin k i) x z ×
                      adjacent-Finitely-Graded-Poset X
                        ( succ-Fin (inl-Fin k i))
                        ( z)
                        ( y)))
                ( two-ℕ))))
