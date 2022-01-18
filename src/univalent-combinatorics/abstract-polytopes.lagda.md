---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.abstract-polytopes where

open import order-theory public
```

## The axioms of Abstract Polytopes

We define abstract polytopes as finitely graded posets satisfying certain axioms. In the classical definition, the grading is a consequence of the axioms. Here, we take finitely graded posets as our starting point

The first axiom of polytopes asserts that polytopes have a least and a largest element. This is already defined as

`least-and-largest-element-finitely-graded-poset-Prop`.

Next, we assert the diamond condition for abstract polytopes.

```agda

diamond-condition-finitely-graded-poset-Prop :
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k) →
  UU-Prop (l1 ⊔ l2)
diamond-condition-finitely-graded-poset-Prop {k = zero-ℕ} X = raise-unit-Prop _
diamond-condition-finitely-graded-poset-Prop {k = succ-ℕ k} X =
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

module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where
  
  diamond-condition-Finitely-Graded-Poset : UU (l1 ⊔ l2)
  diamond-condition-Finitely-Graded-Poset =
    type-Prop (diamond-condition-finitely-graded-poset-Prop X)

  is-prop-diamond-condition-Finitely-Graded-Poset :
    is-prop diamond-condition-Finitely-Graded-Poset
  is-prop-diamond-condition-Finitely-Graded-Poset =
    is-prop-type-Prop (diamond-condition-finitely-graded-poset-Prop X)
```

## Some terminology of polytopes

We introduce the notion of prepolytopes to be finitely graded posets equipped with a least and a largest element, and satisfying the diamond condition. Before we state the remaining conditions of polytopes, we introduce some terminology

```agda

Prepolytope : (l1 l2 : Level) (k : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
Prepolytope l1 l2 k =
  Σ ( Finitely-Graded-Poset l1 l2 k)
    ( λ X →
      least-and-largest-element-Finitely-Graded-Poset X ×
      diamond-condition-Finitely-Graded-Poset X)

module _
  {l1 l2 : Level} {k : ℕ} (X : Prepolytope l1 l2 k)
  where

  finitely-graded-poset-Prepolytope : Finitely-Graded-Poset l1 l2 k
  finitely-graded-poset-Prepolytope = pr1 X

  least-and-largest-element-Prepolytope :
    least-and-largest-element-Finitely-Graded-Poset
      finitely-graded-poset-Prepolytope
  least-and-largest-element-Prepolytope = pr1 (pr2 X)

  least-element-Prepolytope :
    least-element-Finitely-Graded-Poset finitely-graded-poset-Prepolytope
  least-element-Prepolytope = pr1 least-and-largest-element-Prepolytope

  largest-element-Prepolytope :
    largest-element-Finitely-Graded-Poset finitely-graded-poset-Prepolytope
  largest-element-Prepolytope = pr2 least-and-largest-element-Prepolytope

  diamond-condition-Prepolytope :
    diamond-condition-Finitely-Graded-Poset finitely-graded-poset-Prepolytope
  diamond-condition-Prepolytope = pr2 (pr2 X)

  module _
    (i : Fin (succ-ℕ k))
    where

    face-prepolytope-Set : UU-Set l1
    face-prepolytope-Set =
      face-finitely-graded-poset-Set finitely-graded-poset-Prepolytope i

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

    adjancent-prepolytope-Prop : UU-Prop l2
    adjancent-prepolytope-Prop =
      adjacent-finitely-graded-poset-Prop
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

  element-prepolytope-Set : UU-Set l1
  element-prepolytope-Set =
    element-finitely-graded-poset-Set finitely-graded-poset-Prepolytope

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

  path-elements-Prepolytope : (x y : element-Prepolytope) → UU (l1 ⊔ l2)
  path-elements-Prepolytope =
    path-elements-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  refl-path-elements-Prepolytope :
    (x : element-Prepolytope) → path-elements-Prepolytope x x
  refl-path-elements-Prepolytope =
    refl-path-elements-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  concat-path-elements-Prepolytope :
    (x y z : element-Prepolytope) →
    path-elements-Prepolytope y z → path-elements-Prepolytope x y →
    path-elements-Prepolytope x z
  concat-path-elements-Prepolytope =
    concat-path-elements-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  leq-type-path-faces-Prepolytope :
    {i1 i2 : Fin (succ-ℕ k)} (x : face-Prepolytope i1)
    (y : face-Prepolytope i2) → path-faces-Prepolytope x y → leq-Fin i1 i2
  leq-type-path-faces-Prepolytope =
    leq-type-path-faces-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  eq-path-elements-Prepolytope :
    (x y : element-Prepolytope)
    (p : Id (type-element-Prepolytope x) (type-element-Prepolytope y)) →
    path-elements-Prepolytope x y → Id x y
  eq-path-elements-Prepolytope =
    eq-path-elements-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  eq-path-faces-Prepolytope :
    {i : Fin (succ-ℕ k)} (x y : face-Prepolytope i) →
    path-faces-Prepolytope x y → Id x y
  eq-path-faces-Prepolytope =
    eq-path-faces-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  antisymmetric-path-elements-Prepolytope :
    (x y : element-Prepolytope) → path-elements-Prepolytope x y →
    path-elements-Prepolytope y x → Id x y
  antisymmetric-path-elements-Prepolytope =
    antisymmetric-path-elements-Finitely-Graded-Poset
      finitely-graded-poset-Prepolytope

  module _
    (x y : element-Prepolytope)
    where

    leq-prepolytope-Prop : UU-Prop (l1 ⊔ l2)
    leq-prepolytope-Prop =
      leq-finitely-graded-poset-Prop finitely-graded-poset-Prepolytope x y

    leq-Prepolytope : UU (l1 ⊔ l2)
    leq-Prepolytope =
      leq-Finitely-Graded-Poset finitely-graded-poset-Prepolytope x y

    is-prop-leq-Prepolytope : is-prop leq-Prepolytope
    is-prop-leq-Prepolytope =
      is-prop-leq-Finitely-Graded-Poset finitely-graded-poset-Prepolytope x y

  refl-leq-Prepolytope : (x : element-Prepolytope) → leq-Prepolytope x x
  refl-leq-Prepolytope =
    refl-leq-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  transitive-leq-Prepolytope :
    (x y z : element-Prepolytope) →
    leq-Prepolytope y z → leq-Prepolytope x y → leq-Prepolytope x z
  transitive-leq-Prepolytope =
    transitive-leq-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  antisymmetric-leq-Prepolytope :
    (x y : element-Prepolytope) →
    leq-Prepolytope x y → leq-Prepolytope y x → Id x y
  antisymmetric-leq-Prepolytope =
    antisymmetric-leq-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  poset-Prepolytope : Poset l1 (l1 ⊔ l2)
  poset-Prepolytope =
    poset-Finitely-Graded-Poset finitely-graded-poset-Prepolytope
    
  chain-Prepolytope : (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  chain-Prepolytope =
    chain-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  flag-Prepolytope : (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  flag-Prepolytope =
    maximal-chain-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  subtype-flag-Prepolytope :
    {l : Level} (F : flag-Prepolytope l) →
    {i : Fin (succ-ℕ k)} → face-Prepolytope i → UU-Prop l
  subtype-flag-Prepolytope =
    subtype-maximal-chain-Finitely-Graded-Poset
      finitely-graded-poset-Prepolytope

  face-least-element-Prepolytope : face-Prepolytope zero-Fin
  face-least-element-Prepolytope = pr1 least-element-Prepolytope

  element-least-element-Prepolytope : element-Prepolytope
  element-least-element-Prepolytope =
    element-face-Prepolytope face-least-element-Prepolytope

  is-least-element-least-element-Prepolytope :
    (x : element-Prepolytope) →
    leq-Prepolytope element-least-element-Prepolytope x
  is-least-element-least-element-Prepolytope =
    pr2 least-element-Prepolytope

  face-largest-element-Prepolytope : face-Prepolytope neg-one-Fin
  face-largest-element-Prepolytope = pr1 largest-element-Prepolytope

  element-largest-element-Prepolytope : element-Prepolytope
  element-largest-element-Prepolytope =
    element-face-Prepolytope face-largest-element-Prepolytope

  is-largest-element-largest-element-Prepolytope :
    (x : element-Prepolytope) →
    leq-Prepolytope x element-largest-element-Prepolytope
  is-largest-element-largest-element-Prepolytope =
    pr2 largest-element-Prepolytope

  is-contr-face-bottom-dimension-Prepolytope :
    is-contr (face-Prepolytope zero-Fin)
  pr1 is-contr-face-bottom-dimension-Prepolytope =
    face-least-element-Prepolytope
  pr2 is-contr-face-bottom-dimension-Prepolytope x =
    apply-universal-property-trunc-Prop
      ( is-least-element-least-element-Prepolytope (element-face-Prepolytope x))
      ( Id-Prop
        ( face-prepolytope-Set zero-Fin)
        ( face-least-element-Prepolytope)
        ( x))
      ( λ p → eq-path-faces-Prepolytope face-least-element-Prepolytope x p)

  is-contr-face-top-dimension-Prepolytope :
    is-contr (face-Prepolytope neg-one-Fin)
  pr1 is-contr-face-top-dimension-Prepolytope =
    face-largest-element-Prepolytope
  pr2 is-contr-face-top-dimension-Prepolytope x =
    apply-universal-property-trunc-Prop
      ( is-largest-element-largest-element-Prepolytope
        ( element-face-Prepolytope x))
      ( Id-Prop
        ( face-prepolytope-Set neg-one-Fin)
        ( face-largest-element-Prepolytope)
        ( x))
      ( λ p →
        inv (eq-path-faces-Prepolytope x face-largest-element-Prepolytope p))
```

## Axiom P2 of polytopes

The second axiom of polytopes asserts that every maximal chain has k elements. Here, we will assert that every maximal chain has exactly one face of each dimension.


```agda

module _
  {l1 l2 : Level} (l : Level) {k : ℕ} (X : Prepolytope l1 l2 k)
  where

  condition-P2-prepolytope-Prop : UU-Prop (l1 ⊔ l2 ⊔ lsuc l)
  condition-P2-prepolytope-Prop =
    Π-Prop
      ( flag-Prepolytope X l)
      ( λ F →
        Π-Prop
          ( Fin (succ-ℕ k))
          ( λ i →
            is-contr-Prop
              ( Σ ( face-Prepolytope X i)
                  ( λ x → type-Prop (subtype-flag-Prepolytope X F x)))))

  condition-P2-Prepolytope : UU (l1 ⊔ l2 ⊔ lsuc l)
  condition-P2-Prepolytope = type-Prop condition-P2-prepolytope-Prop

  is-prop-condition-P2-Prepolytope : is-prop condition-P2-Prepolytope
  is-prop-condition-P2-Prepolytope =
    is-prop-type-Prop condition-P2-prepolytope-Prop
```

## The definition of abstract polytopes

```agda

Polytope :
  (l1 l2 l3 : Level) (k : ℕ) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Polytope l1 l2 l3 k =
  Σ ( Prepolytope l1 l2 k)
    ( λ X →
      ( condition-P2-Prepolytope l3 X) ×
      unit)
