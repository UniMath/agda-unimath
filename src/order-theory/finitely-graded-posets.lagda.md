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
    
    face-Finitely-Graded-Poset-Set : UU-Set l1
    face-Finitely-Graded-Poset-Set = pr1 X i

    face-Finitely-Graded-Poset : UU l1
    face-Finitely-Graded-Poset =
      type-Set face-Finitely-Graded-Poset-Set

    is-set-face-Finitely-Graded-Poset :
      is-set face-Finitely-Graded-Poset
    is-set-face-Finitely-Graded-Poset =
      is-set-type-Set face-Finitely-Graded-Poset-Set

  module _
    (i : Fin k) (y : face-Finitely-Graded-Poset (inl-Fin k i))
    (z : face-Finitely-Graded-Poset (succ-Fin (inl-Fin k i)))
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

  vertex-Finitely-Graded-Poset-Set : UU-Set l1
  vertex-Finitely-Graded-Poset-Set =
    Σ-Set (Fin-Set (succ-ℕ k)) face-Finitely-Graded-Poset-Set

  vertex-Finitely-Graded-Poset : UU l1
  vertex-Finitely-Graded-Poset = type-Set vertex-Finitely-Graded-Poset-Set

  is-set-vertex-Finitely-Graded-Poset : is-set vertex-Finitely-Graded-Poset
  is-set-vertex-Finitely-Graded-Poset =
    is-set-type-Set vertex-Finitely-Graded-Poset-Set

  vertex-face-Finitely-Graded-Poset :
    {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset i →
    vertex-Finitely-Graded-Poset
  vertex-face-Finitely-Graded-Poset {i} x = pair i x

  type-vertex-Finitely-Graded-Poset :
    vertex-Finitely-Graded-Poset → Fin (succ-ℕ k)
  type-vertex-Finitely-Graded-Poset (pair i x) = i

  face-vertex-Finitely-Graded-Poset :
    (x : vertex-Finitely-Graded-Poset) →
    face-Finitely-Graded-Poset (type-vertex-Finitely-Graded-Poset x)
  face-vertex-Finitely-Graded-Poset (pair i x) = x

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
    (x y : vertex-Finitely-Graded-Poset) → UU (l1 ⊔ l2)
  path-vertices-Finitely-Graded-Poset (pair i x) (pair j y) =
    path-faces-Finitely-Graded-Poset x y

  refl-path-vertices-Finitely-Graded-Poset :
    (x : vertex-Finitely-Graded-Poset) → path-vertices-Finitely-Graded-Poset x x
  refl-path-vertices-Finitely-Graded-Poset x =
    refl-path-faces-Finitely-Graded-Poset

  concat-path-vertices-Finitely-Graded-Poset :
    (x y z : vertex-Finitely-Graded-Poset) →
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
```

### Antisymmetry of path-vertices-Finitely-Graded-Poset

```agda
eq-path-vertices-Finitely-Graded-Poset :
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k)
  (x y : vertex-Finitely-Graded-Poset k X) →
  (p : Id (type-vertex-Finitely-Graded-Poset k X x)
          (type-vertex-Finitely-Graded-Poset k X y)) →
  path-vertices-Finitely-Graded-Poset k X x y → Id x y
eq-path-vertices-Finitely-Graded-Poset k X (pair i1 x) (pair .i1 .x) p
  refl-path-faces-Finitely-Graded-Poset = refl
eq-path-vertices-Finitely-Graded-Poset (succ-ℕ k) X (pair i1 x)
  (pair .(succ-Fin (inl-Fin (succ-ℕ k) i2)) y) p
  (cons-path-faces-Finitely-Graded-Poset {i2} {z} H K) =
  ex-falso
    ( has-no-fixed-points-succ-Fin
      ( inl-Fin (succ-ℕ k) i2)
      ( λ q → is-nonzero-succ-ℕ k (is-injective-succ-ℕ q))
      ( antisymmetric-leq-Fin
        ( transitive-leq-Fin
          { k = succ-ℕ (succ-ℕ k)}
          { x = succ-Fin (inl-Fin (succ-ℕ k) i2)}
          { i1}
          ( tr
            ( leq-Fin (succ-Fin (inl-Fin (succ-ℕ k) i2)))
            ( inv p)
            ( refl-leq-Fin (succ-Fin (inl-Fin (succ-ℕ k) i2))))
          ( leq-type-path-faces-Finitely-Graded-Poset
            ( succ-ℕ k) X x z K))
        ( leq-succ-Fin i2)))

antisymmetric-path-vertices-Finitely-Graded-Poset :
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k) →
  (x y : vertex-Finitely-Graded-Poset k X) →
  path-vertices-Finitely-Graded-Poset k X x y →
  path-vertices-Finitely-Graded-Poset k X y x →
  Id x y
antisymmetric-path-vertices-Finitely-Graded-Poset
  k X (pair i x) (pair j y) H K =
  eq-path-vertices-Finitely-Graded-Poset k X (pair i x) (pair j y)
    ( antisymmetric-leq-Fin
      ( leq-type-path-faces-Finitely-Graded-Poset k X x y H)
      ( leq-type-path-faces-Finitely-Graded-Poset k X y x K))
    ( H)
```

### Poset structure on vertex-Finitely-Graded-Poset

```agda

module _
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    (x y : vertex-Finitely-Graded-Poset k X)
    where
    
    leq-Finitely-Graded-Poset-Prop : UU-Prop (l1 ⊔ l2)
    leq-Finitely-Graded-Poset-Prop =
      trunc-Prop (path-vertices-Finitely-Graded-Poset k X x y)

    leq-Finitely-Graded-Poset : UU (l1 ⊔ l2)
    leq-Finitely-Graded-Poset = type-Prop leq-Finitely-Graded-Poset-Prop

    is-prop-leq-Finitely-Graded-Poset : is-prop leq-Finitely-Graded-Poset
    is-prop-leq-Finitely-Graded-Poset =
      is-prop-type-Prop leq-Finitely-Graded-Poset-Prop

  refl-leq-Finitely-Graded-Poset :
    (x : vertex-Finitely-Graded-Poset k X) → leq-Finitely-Graded-Poset x x
  refl-leq-Finitely-Graded-Poset x =
    unit-trunc-Prop (refl-path-vertices-Finitely-Graded-Poset k X x)

  transitive-leq-Finitely-Graded-Poset :
    (x y z : vertex-Finitely-Graded-Poset k X) →
    leq-Finitely-Graded-Poset y z → leq-Finitely-Graded-Poset x y →
    leq-Finitely-Graded-Poset x z
  transitive-leq-Finitely-Graded-Poset x y z H K =
    apply-universal-property-trunc-Prop H
      ( leq-Finitely-Graded-Poset-Prop x z)
      ( λ L →
        apply-universal-property-trunc-Prop K
          ( leq-Finitely-Graded-Poset-Prop x z)
          ( λ M →
            unit-trunc-Prop
              ( concat-path-vertices-Finitely-Graded-Poset k X x y z L M)))

  antisymmetric-leq-Finitely-Graded-Poset :
    (x y : vertex-Finitely-Graded-Poset k X) →
    leq-Finitely-Graded-Poset x y → leq-Finitely-Graded-Poset y x → Id x y
  antisymmetric-leq-Finitely-Graded-Poset x y H K =
    apply-universal-property-trunc-Prop H
      ( Id-Prop (vertex-Finitely-Graded-Poset-Set k X) x y)
      ( λ L →
        apply-universal-property-trunc-Prop K
          ( Id-Prop (vertex-Finitely-Graded-Poset-Set k X) x y)
          ( λ M →
            antisymmetric-path-vertices-Finitely-Graded-Poset k X x y L M))
  
  poset-Finitely-Graded-Poset : Poset l1 (l1 ⊔ l2)
  pr1 poset-Finitely-Graded-Poset = vertex-Finitely-Graded-Poset k X
  pr1 (pr2 poset-Finitely-Graded-Poset) = leq-Finitely-Graded-Poset-Prop
  pr1 (pr1 (pr2 (pr2 poset-Finitely-Graded-Poset))) =
    refl-leq-Finitely-Graded-Poset
  pr2 (pr1 (pr2 (pr2 poset-Finitely-Graded-Poset))) =
    transitive-leq-Finitely-Graded-Poset
  pr2 (pr2 (pr2 poset-Finitely-Graded-Poset)) =
    antisymmetric-leq-Finitely-Graded-Poset
