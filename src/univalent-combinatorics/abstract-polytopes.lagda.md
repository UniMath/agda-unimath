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

  type-element-Prepolytope :
    element-Prepolytope → Fin (succ-ℕ k)
  type-element-Prepolytope =
    type-element-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  face-element-Prepolytope :
    (x : element-Prepolytope) → face-Prepolytope (type-element-Prepolytope x)
  face-element-Prepolytope =
    face-element-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  path-faces-Prepolytope :
    {i j : Fin (succ-ℕ k)} →
    face-Prepolytope i → face-Prepolytope j → UU (l1 ⊔ l2)
  path-faces-Prepolytope x y =
    path-faces-Finitely-Graded-Poset finitely-graded-poset-Prepolytope x y

  tr-refl-path-faces-Preposet :
    {i j : Fin (succ-ℕ k)} (p : Id j i) (x : face-Prepolytope j) →
    path-faces-Prepolytope (tr face-Prepolytope p x) x
  tr-refl-path-faces-Preposet =
    tr-refl-path-faces-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  concat-path-faces-Prepolytope :
    {i1 i2 i3 : Fin (succ-ℕ k)} {x : face-Prepolytope i1}
    {y : face-Prepolytope i2} {z : face-Prepolytope i3} →
    path-faces-Prepolytope y z → path-faces-Prepolytope x y →
    path-faces-Prepolytope x z
  concat-path-faces-Prepolytope =
    concat-path-faces-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  path-vertices-Prepolytope : (x y : element-Prepolytope) → UU (l1 ⊔ l2)
  path-vertices-Prepolytope =
    path-vertices-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  refl-path-vertices-Prepolytope :
    (x : element-Prepolytope) → path-vertices-Prepolytope x x
  refl-path-vertices-Prepolytope =
    refl-path-vertices-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  concat-path-vertices-Prepolytope :
    (x y z : element-Prepolytope) →
    path-vertices-Prepolytope y z → path-vertices-Prepolytope x y →
    path-vertices-Prepolytope x z
  concat-path-vertices-Prepolytope =
    concat-path-vertices-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  leq-type-path-faces-Prepolytope :
    {i1 i2 : Fin (succ-ℕ k)} (x : face-Prepolytope i1)
    (y : face-Prepolytope i2) → path-faces-Prepolytope x y → leq-Fin i1 i2
  leq-type-path-faces-Prepolytope =
    leq-type-path-faces-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  chain-Prepolytope :
    (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  chain-Prepolytope =
    chain-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  flag-Prepolytope :
    (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  flag-Prepolytope =
    maximal-chain-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  subtype-flag-Prepolytope :
    {l : Level} (F : flag-Prepolytope l) →
    {i : Fin (succ-ℕ k)} → face-Prepolytope i → UU-Prop l
  subtype-flag-Prepolytope =
    subtype-maximal-chain-Finitely-Graded-Poset
      finitely-graded-poset-Prepolytope

```

  (P3) Every flag has precisely one face in each dimension

```agda

module _
  {l1 l2 l3 : Level} {k : ℕ} (X : Prepolytope l1 l2 l3 k)
  where

  P3-Polytope-Prop : (l : Level) → UU-Prop (l1 ⊔ l2 ⊔ lsuc l)
  P3-Polytope-Prop l =
    Π-Prop
      ( flag-Prepolytope k X l)
      ( λ F →
        Π-Prop
          ( Fin (succ-ℕ k))
          ( λ i →
            is-contr-Prop
              ( Σ ( face-Prepolytope k X i)
                  ( λ x → type-Prop (subtype-flag-Prepolytope k X F x)))))

  P3-Polytope : (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  P3-Polytope l = type-Prop (P3-Polytope-Prop l)

  is-prop-P3-Polytope : (l : Level) → is-prop (P3-Polytope l)
  is-prop-P3-Polytope l = is-prop-type-Prop (P3-Polytope-Prop l)
```

  (P4) We state the diamond condition

```agda

diamond-condition-Finitely-Graded-Poset-Prop :
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k) →
  UU-Prop (l1 ⊔ l2)
diamond-condition-Finitely-Graded-Poset-Prop zero-ℕ X = raise-unit-Prop _
diamond-condition-Finitely-Graded-Poset-Prop (succ-ℕ k) X =
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

```

## The definition of abstract polytopes

```agda

Polytope :
  (l1 l2 l3 l4 : Level) (k : ℕ) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4)
Polytope l1 l2 l3 l4 k =
  Σ ( Prepolytope l1 l2 l3 k)
    ( λ X →
      ( P3-Polytope X l4) ×
      ( type-Prop (diamond-condition-Finitely-Graded-Poset-Prop k (pr1 X))))
