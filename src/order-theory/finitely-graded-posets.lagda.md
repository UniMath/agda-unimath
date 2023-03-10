# Finitely graded posets

```agda
module order-theory.finitely-graded-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.functions
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import order-theory.largest-elements-posets
open import order-theory.least-elements-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A finitely graded poset consists of a family of types indexed by `Fin (succ-ℕ k)` equipped with an ordering relation from `Fin (inl i)` to `Fin (succ-Fin (inl i))` for each `i : Fin k`.

```agda

Finitely-Graded-Poset : (l1 l2 : Level) (k : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
Finitely-Graded-Poset l1 l2 k =
  Σ ( Fin (succ-ℕ k) → Set l1)
    ( λ X →
      (i : Fin k) → type-Set (X (inl-Fin k i)) →
      type-Set (X (succ-Fin (succ-ℕ k) (inl-Fin k i))) → Prop l2)

module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    (i : Fin (succ-ℕ k))
    where

    face-finitely-graded-poset-Set : Set l1
    face-finitely-graded-poset-Set = pr1 X i

    face-Finitely-Graded-Poset : UU l1
    face-Finitely-Graded-Poset =
      type-Set face-finitely-graded-poset-Set

    is-set-face-Finitely-Graded-Poset :
      is-set face-Finitely-Graded-Poset
    is-set-face-Finitely-Graded-Poset =
      is-set-type-Set face-finitely-graded-poset-Set

  module _
    (i : Fin k) (y : face-Finitely-Graded-Poset (inl-Fin k i))
    (z : face-Finitely-Graded-Poset (succ-Fin (succ-ℕ k) (inl-Fin k i)))
    where

    adjacent-finitely-graded-poset-Prop : Prop l2
    adjacent-finitely-graded-poset-Prop = pr2 X i y z

    adjacent-Finitely-Graded-Poset : UU l2
    adjacent-Finitely-Graded-Poset =
      type-Prop adjacent-finitely-graded-poset-Prop

    is-prop-adjacent-Finitely-Graded-Poset :
      is-prop adjacent-Finitely-Graded-Poset
    is-prop-adjacent-Finitely-Graded-Poset =
      is-prop-type-Prop adjacent-finitely-graded-poset-Prop

  element-finitely-graded-poset-Set : Set l1
  element-finitely-graded-poset-Set =
    Σ-Set (Fin-Set (succ-ℕ k)) face-finitely-graded-poset-Set

  element-Finitely-Graded-Poset : UU l1
  element-Finitely-Graded-Poset = type-Set element-finitely-graded-poset-Set

  is-set-element-Finitely-Graded-Poset : is-set element-Finitely-Graded-Poset
  is-set-element-Finitely-Graded-Poset =
    is-set-type-Set element-finitely-graded-poset-Set

  element-face-Finitely-Graded-Poset :
    {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset i →
    element-Finitely-Graded-Poset
  element-face-Finitely-Graded-Poset {i} x = pair i x

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
          {z : face-Finitely-Graded-Poset (succ-Fin (succ-ℕ k) (inl-Fin k j))} →
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

  path-elements-Finitely-Graded-Poset :
    (x y : element-Finitely-Graded-Poset) → UU (l1 ⊔ l2)
  path-elements-Finitely-Graded-Poset (pair i x) (pair j y) =
    path-faces-Finitely-Graded-Poset x y

  refl-path-elements-Finitely-Graded-Poset :
    (x : element-Finitely-Graded-Poset) → path-elements-Finitely-Graded-Poset x x
  refl-path-elements-Finitely-Graded-Poset x =
    refl-path-faces-Finitely-Graded-Poset

  concat-path-elements-Finitely-Graded-Poset :
    (x y z : element-Finitely-Graded-Poset) →
    path-elements-Finitely-Graded-Poset y z →
    path-elements-Finitely-Graded-Poset x y →
    path-elements-Finitely-Graded-Poset x z
  concat-path-elements-Finitely-Graded-Poset x y z =
    concat-path-faces-Finitely-Graded-Poset

  leq-type-path-faces-Finitely-Graded-Poset :
    {i1 i2 : Fin (succ-ℕ k)} (x : face-Finitely-Graded-Poset i1)
    (y : face-Finitely-Graded-Poset i2) →
    path-faces-Finitely-Graded-Poset x y → leq-Fin (succ-ℕ k) i1 i2
  leq-type-path-faces-Finitely-Graded-Poset {i1} x .x
    refl-path-faces-Finitely-Graded-Poset = refl-leq-Fin (succ-ℕ k) i1
  leq-type-path-faces-Finitely-Graded-Poset {i1} x y
    ( cons-path-faces-Finitely-Graded-Poset {i3} {z} H K) =
     transitive-leq-Fin
       ( succ-ℕ k)
       ( i1)
       ( inl-Fin k i3)
       ( succ-Fin (succ-ℕ k) (inl-Fin k i3))
       ( leq-succ-Fin k i3)
       ( leq-type-path-faces-Finitely-Graded-Poset x z K)
```

### Antisymmetry of path-elements-Finitely-Graded-Poset

```agda
eq-path-elements-Finitely-Graded-Poset :
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  (x y : element-Finitely-Graded-Poset X) →
  (p : Id (type-element-Finitely-Graded-Poset X x)
          (type-element-Finitely-Graded-Poset X y)) →
  path-elements-Finitely-Graded-Poset X x y → Id x y
eq-path-elements-Finitely-Graded-Poset {k} X (pair i1 x) (pair .i1 .x) p
  refl-path-faces-Finitely-Graded-Poset = refl
eq-path-elements-Finitely-Graded-Poset {k = succ-ℕ k} X (pair i1 x)
  (pair .(succ-Fin (succ-ℕ (succ-ℕ k)) (inl-Fin (succ-ℕ k) i2)) y) p
  (cons-path-faces-Finitely-Graded-Poset {i2} {z} H K) =
  ex-falso
    ( has-no-fixed-points-succ-Fin
      { succ-ℕ (succ-ℕ k)}
      ( inl-Fin (succ-ℕ k) i2)
      ( λ (q : is-one-ℕ (succ-ℕ (succ-ℕ k))) →
        is-nonzero-succ-ℕ k (is-injective-succ-ℕ q))
      ( antisymmetric-leq-Fin
        ( succ-ℕ (succ-ℕ k))
        ( succ-Fin (succ-ℕ (succ-ℕ k)) (inl-Fin (succ-ℕ k) i2))
        ( inl-Fin (succ-ℕ k) i2)
        ( transitive-leq-Fin
          ( succ-ℕ (succ-ℕ k))
          ( skip-zero-Fin (succ-ℕ k) i2)
          ( i1)
          ( inl i2)
          ( leq-type-path-faces-Finitely-Graded-Poset X x z K)
          ( tr
            ( leq-Fin
              ( succ-ℕ (succ-ℕ k))
              ( succ-Fin (succ-ℕ (succ-ℕ k)) (inl-Fin (succ-ℕ k) i2)))
            ( inv p)
            ( refl-leq-Fin
              ( succ-ℕ (succ-ℕ k))
              ( succ-Fin (succ-ℕ (succ-ℕ k)) (inl-Fin (succ-ℕ k) i2)))))
        ( leq-succ-Fin (succ-ℕ k) i2)))

module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  abstract
    eq-path-faces-Finitely-Graded-Poset :
      {i : Fin (succ-ℕ k)} (x y : face-Finitely-Graded-Poset X i) →
      path-faces-Finitely-Graded-Poset X x y → Id x y
    eq-path-faces-Finitely-Graded-Poset {i} x y H =
      map-left-unit-law-Σ-is-contr
        ( is-proof-irrelevant-is-prop
          ( is-set-Fin (succ-ℕ k) i i)
          ( refl))
        ( refl)
        ( pair-eq-Σ
          ( eq-path-elements-Finitely-Graded-Poset X
            ( element-face-Finitely-Graded-Poset X x)
            ( element-face-Finitely-Graded-Poset X y)
            ( refl)
            ( H)))

  antisymmetric-path-elements-Finitely-Graded-Poset :
    (x y : element-Finitely-Graded-Poset X) →
    path-elements-Finitely-Graded-Poset X x y →
    path-elements-Finitely-Graded-Poset X y x →
    Id x y
  antisymmetric-path-elements-Finitely-Graded-Poset (pair i x) (pair j y) H K =
    eq-path-elements-Finitely-Graded-Poset X (pair i x) (pair j y)
      ( antisymmetric-leq-Fin (succ-ℕ k)
        ( type-element-Finitely-Graded-Poset X (pair i x))
        ( type-element-Finitely-Graded-Poset X (pair j y))
        ( leq-type-path-faces-Finitely-Graded-Poset X x y H)
        ( leq-type-path-faces-Finitely-Graded-Poset X y x K))
      ( H)
```

### Poset structure on element-Finitely-Graded-Poset

```agda

module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    (x y : element-Finitely-Graded-Poset X)
    where

    leq-finitely-graded-poset-Prop : Prop (l1 ⊔ l2)
    leq-finitely-graded-poset-Prop =
      trunc-Prop (path-elements-Finitely-Graded-Poset X x y)

    leq-Finitely-Graded-Poset : UU (l1 ⊔ l2)
    leq-Finitely-Graded-Poset = type-Prop leq-finitely-graded-poset-Prop

    is-prop-leq-Finitely-Graded-Poset : is-prop leq-Finitely-Graded-Poset
    is-prop-leq-Finitely-Graded-Poset =
      is-prop-type-Prop leq-finitely-graded-poset-Prop

  refl-leq-Finitely-Graded-Poset :
    (x : element-Finitely-Graded-Poset X) → leq-Finitely-Graded-Poset x x
  refl-leq-Finitely-Graded-Poset x =
    unit-trunc-Prop (refl-path-elements-Finitely-Graded-Poset X x)

  transitive-leq-Finitely-Graded-Poset :
    (x y z : element-Finitely-Graded-Poset X) →
    leq-Finitely-Graded-Poset y z → leq-Finitely-Graded-Poset x y →
    leq-Finitely-Graded-Poset x z
  transitive-leq-Finitely-Graded-Poset x y z H K =
    apply-universal-property-trunc-Prop H
      ( leq-finitely-graded-poset-Prop x z)
      ( λ L →
        apply-universal-property-trunc-Prop K
          ( leq-finitely-graded-poset-Prop x z)
          ( λ M →
            unit-trunc-Prop
              ( concat-path-elements-Finitely-Graded-Poset X x y z L M)))

  antisymmetric-leq-Finitely-Graded-Poset :
    (x y : element-Finitely-Graded-Poset X) →
    leq-Finitely-Graded-Poset x y → leq-Finitely-Graded-Poset y x → Id x y
  antisymmetric-leq-Finitely-Graded-Poset x y H K =
    apply-universal-property-trunc-Prop H
      ( Id-Prop (element-finitely-graded-poset-Set X) x y)
      ( λ L →
        apply-universal-property-trunc-Prop K
          ( Id-Prop (element-finitely-graded-poset-Set X) x y)
          ( λ M →
            antisymmetric-path-elements-Finitely-Graded-Poset X x y L M))

  poset-Finitely-Graded-Poset : Poset l1 (l1 ⊔ l2)
  pr1 poset-Finitely-Graded-Poset = element-Finitely-Graded-Poset X
  pr1 (pr2 poset-Finitely-Graded-Poset) = leq-finitely-graded-poset-Prop
  pr1 (pr1 (pr2 (pr2 poset-Finitely-Graded-Poset))) =
    refl-leq-Finitely-Graded-Poset
  pr2 (pr1 (pr2 (pr2 poset-Finitely-Graded-Poset))) =
    transitive-leq-Finitely-Graded-Poset
  pr2 (pr2 (pr2 poset-Finitely-Graded-Poset)) =
    antisymmetric-leq-Finitely-Graded-Poset
```

### Least and largest elements in finitely graded posets

We make sure that the least element is a face of type zero-Fin, and that the largest element is a face of type neg-one-Fin.

```agda
module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    (x : face-Finitely-Graded-Poset X (zero-Fin k))
    where

    is-least-element-finitely-graded-poset-Prop : Prop (l1 ⊔ l2)
    is-least-element-finitely-graded-poset-Prop =
      is-least-element-poset-Prop
        ( poset-Finitely-Graded-Poset X)
        ( element-face-Finitely-Graded-Poset X x)

    is-least-element-Finitely-Graded-Poset : UU (l1 ⊔ l2)
    is-least-element-Finitely-Graded-Poset =
      is-least-element-Poset
        ( poset-Finitely-Graded-Poset X)
        ( element-face-Finitely-Graded-Poset X x)

    is-prop-is-least-element-Finitely-Graded-Poset :
      is-prop is-least-element-Finitely-Graded-Poset
    is-prop-is-least-element-Finitely-Graded-Poset =
      is-prop-is-least-element-Poset
        ( poset-Finitely-Graded-Poset X)
        ( element-face-Finitely-Graded-Poset X x)

  least-element-Finitely-Graded-Poset : UU (l1 ⊔ l2)
  least-element-Finitely-Graded-Poset =
    Σ ( face-Finitely-Graded-Poset X (zero-Fin k))
      ( is-least-element-Finitely-Graded-Poset)

  all-elements-equal-least-element-Finitely-Graded-Poset :
    all-elements-equal least-element-Finitely-Graded-Poset
  all-elements-equal-least-element-Finitely-Graded-Poset (pair x H) (pair y K) =
    eq-type-subtype
      ( is-least-element-finitely-graded-poset-Prop)
      ( apply-universal-property-trunc-Prop
        ( H (element-face-Finitely-Graded-Poset X y))
        ( Id-Prop (face-finitely-graded-poset-Set X (zero-Fin k)) x y)
        ( eq-path-faces-Finitely-Graded-Poset X x y))

  is-prop-least-element-Finitely-Graded-Poset :
    is-prop least-element-Finitely-Graded-Poset
  is-prop-least-element-Finitely-Graded-Poset =
    is-prop-all-elements-equal
      all-elements-equal-least-element-Finitely-Graded-Poset

  least-element-finitely-graded-poset-Prop : Prop (l1 ⊔ l2)
  pr1 least-element-finitely-graded-poset-Prop =
    least-element-Finitely-Graded-Poset
  pr2 least-element-finitely-graded-poset-Prop =
    is-prop-least-element-Finitely-Graded-Poset

  module _
    (x : face-Finitely-Graded-Poset X (neg-one-Fin k))
    where

    is-largest-element-finitely-graded-poset-Prop : Prop (l1 ⊔ l2)
    is-largest-element-finitely-graded-poset-Prop =
      is-largest-element-poset-Prop
        ( poset-Finitely-Graded-Poset X)
        ( element-face-Finitely-Graded-Poset X x)

    is-largest-element-Finitely-Graded-Poset : UU (l1 ⊔ l2)
    is-largest-element-Finitely-Graded-Poset =
      is-largest-element-Poset
        ( poset-Finitely-Graded-Poset X)
        ( element-face-Finitely-Graded-Poset X x)

    is-prop-is-largest-element-Finitely-Graded-Poset :
      is-prop is-largest-element-Finitely-Graded-Poset
    is-prop-is-largest-element-Finitely-Graded-Poset =
      is-prop-is-largest-element-Poset
        ( poset-Finitely-Graded-Poset X)
        ( element-face-Finitely-Graded-Poset X x)

  largest-element-Finitely-Graded-Poset : UU (l1 ⊔ l2)
  largest-element-Finitely-Graded-Poset =
    Σ ( face-Finitely-Graded-Poset X (neg-one-Fin k))
      ( is-largest-element-Finitely-Graded-Poset)

  all-elements-equal-largest-element-Finitely-Graded-Poset :
    all-elements-equal largest-element-Finitely-Graded-Poset
  all-elements-equal-largest-element-Finitely-Graded-Poset
    (pair x H) (pair y K) =
    eq-type-subtype
      ( is-largest-element-finitely-graded-poset-Prop)
      ( apply-universal-property-trunc-Prop
        ( K (element-face-Finitely-Graded-Poset X x))
        ( Id-Prop (face-finitely-graded-poset-Set X (neg-one-Fin k)) x y)
        ( eq-path-faces-Finitely-Graded-Poset X x y))

  is-prop-largest-element-Finitely-Graded-Poset :
    is-prop largest-element-Finitely-Graded-Poset
  is-prop-largest-element-Finitely-Graded-Poset =
    is-prop-all-elements-equal
      all-elements-equal-largest-element-Finitely-Graded-Poset

  largest-element-finitely-graded-poset-Prop : Prop (l1 ⊔ l2)
  pr1 largest-element-finitely-graded-poset-Prop =
    largest-element-Finitely-Graded-Poset
  pr2 largest-element-finitely-graded-poset-Prop =
    is-prop-largest-element-Finitely-Graded-Poset

  least-and-largest-element-finitely-graded-poset-Prop : Prop (l1 ⊔ l2)
  least-and-largest-element-finitely-graded-poset-Prop =
    prod-Prop
      least-element-finitely-graded-poset-Prop
      largest-element-finitely-graded-poset-Prop

  least-and-largest-element-Finitely-Graded-Poset : UU (l1 ⊔ l2)
  least-and-largest-element-Finitely-Graded-Poset =
    type-Prop least-and-largest-element-finitely-graded-poset-Prop

  is-prop-least-and-largest-element-Finitely-Graded-Poset :
    is-prop least-and-largest-element-Finitely-Graded-Poset
  is-prop-least-and-largest-element-Finitely-Graded-Poset =
    is-prop-type-Prop least-and-largest-element-finitely-graded-poset-Prop
```

## Finitely graded subposets

```agda

module _
  {l1 l2 l3 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  (S : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3)
  where

  module _
    (i : Fin (succ-ℕ k))
    where

    face-set-Finitely-Graded-Subposet : Set (l1 ⊔ l3)
    face-set-Finitely-Graded-Subposet =
      Σ-Set
        ( face-finitely-graded-poset-Set X i)
        ( λ x → set-Prop (S x))

    face-Finitely-Graded-Subposet : UU (l1 ⊔ l3)
    face-Finitely-Graded-Subposet = type-Set face-set-Finitely-Graded-Subposet

    is-set-face-Finitely-Graded-Subposet : is-set face-Finitely-Graded-Subposet
    is-set-face-Finitely-Graded-Subposet =
      is-set-type-Set face-set-Finitely-Graded-Subposet

    eq-face-Finitely-Graded-Subposet :
      (x y : face-Finitely-Graded-Subposet) → Id (pr1 x) (pr1 y) → Id x y
    eq-face-Finitely-Graded-Subposet x y = eq-type-subtype S

    emb-face-Finitely-Graded-Subposet :
      face-Finitely-Graded-Subposet ↪ face-Finitely-Graded-Poset X i
    emb-face-Finitely-Graded-Subposet = emb-subtype S

    map-emb-face-Finitely-Graded-Subposet :
      face-Finitely-Graded-Subposet → face-Finitely-Graded-Poset X i
    map-emb-face-Finitely-Graded-Subposet =
      map-emb emb-face-Finitely-Graded-Subposet

    is-emb-map-emb-face-Finitely-Graded-Subposet :
      is-emb map-emb-face-Finitely-Graded-Subposet
    is-emb-map-emb-face-Finitely-Graded-Subposet =
      is-emb-map-emb emb-face-Finitely-Graded-Subposet

  module _
    (i : Fin k) (y : face-Finitely-Graded-Subposet (inl-Fin k i))
    (z : face-Finitely-Graded-Subposet (succ-Fin (succ-ℕ k) (inl-Fin k i)))
    where

    adjacent-finitely-graded-subposet-Prop : Prop l2
    adjacent-finitely-graded-subposet-Prop =
      adjacent-finitely-graded-poset-Prop X i (pr1 y) (pr1 z)

    adjacent-Finitely-Graded-Subposet : UU l2
    adjacent-Finitely-Graded-Subposet =
      type-Prop adjacent-finitely-graded-subposet-Prop

    is-prop-adjacent-Finitely-Graded-Subposet :
      is-prop adjacent-Finitely-Graded-Subposet
    is-prop-adjacent-Finitely-Graded-Subposet =
      is-prop-type-Prop adjacent-finitely-graded-subposet-Prop

  element-set-Finitely-Graded-Subposet : Set (l1 ⊔ l3)
  element-set-Finitely-Graded-Subposet =
    Σ-Set (Fin-Set (succ-ℕ k)) face-set-Finitely-Graded-Subposet

  element-Finitely-Graded-Subposet : UU (l1 ⊔ l3)
  element-Finitely-Graded-Subposet =
    type-Set element-set-Finitely-Graded-Subposet

  emb-element-Finitely-Graded-Subposet :
    element-Finitely-Graded-Subposet ↪ element-Finitely-Graded-Poset X
  emb-element-Finitely-Graded-Subposet =
    tot-emb emb-face-Finitely-Graded-Subposet

  map-emb-element-Finitely-Graded-Subposet :
    element-Finitely-Graded-Subposet → element-Finitely-Graded-Poset X
  map-emb-element-Finitely-Graded-Subposet =
    map-emb emb-element-Finitely-Graded-Subposet

  is-emb-map-emb-element-Finitely-Graded-Subposet :
    is-emb map-emb-element-Finitely-Graded-Subposet
  is-emb-map-emb-element-Finitely-Graded-Subposet =
    is-emb-map-emb emb-element-Finitely-Graded-Subposet

  is-injective-map-emb-element-Finitely-Graded-Subposet :
    is-injective map-emb-element-Finitely-Graded-Subposet
  is-injective-map-emb-element-Finitely-Graded-Subposet =
    is-injective-is-emb is-emb-map-emb-element-Finitely-Graded-Subposet

  is-set-element-Finitely-Graded-Subposet :
    is-set element-Finitely-Graded-Subposet
  is-set-element-Finitely-Graded-Subposet =
    is-set-type-Set element-set-Finitely-Graded-Subposet

  leq-finitely-graded-subposet-Prop :
    (x y : element-Finitely-Graded-Subposet) → Prop (l1 ⊔ l2)
  leq-finitely-graded-subposet-Prop x y =
    leq-finitely-graded-poset-Prop X
      ( map-emb-element-Finitely-Graded-Subposet x)
      ( map-emb-element-Finitely-Graded-Subposet y)

  leq-Finitely-Graded-Subposet :
    (x y : element-Finitely-Graded-Subposet) → UU (l1 ⊔ l2)
  leq-Finitely-Graded-Subposet x y =
    type-Prop (leq-finitely-graded-subposet-Prop x y)

  is-prop-leq-Finitely-Graded-Subposet :
    (x y : element-Finitely-Graded-Subposet) →
    is-prop (leq-Finitely-Graded-Subposet x y)
  is-prop-leq-Finitely-Graded-Subposet x y =
    is-prop-type-Prop (leq-finitely-graded-subposet-Prop x y)

  refl-leq-Finitely-Graded-Subposet :
    (x : element-Finitely-Graded-Subposet) → leq-Finitely-Graded-Subposet x x
  refl-leq-Finitely-Graded-Subposet x =
    refl-leq-Finitely-Graded-Poset X
      ( map-emb-element-Finitely-Graded-Subposet x)

  transitive-leq-Finitely-Graded-Subposet :
    (x y z : element-Finitely-Graded-Subposet) →
    leq-Finitely-Graded-Subposet y z → leq-Finitely-Graded-Subposet x y →
    leq-Finitely-Graded-Subposet x z
  transitive-leq-Finitely-Graded-Subposet x y z =
    transitive-leq-Finitely-Graded-Poset X
      ( map-emb-element-Finitely-Graded-Subposet x)
      ( map-emb-element-Finitely-Graded-Subposet y)
      ( map-emb-element-Finitely-Graded-Subposet z)

  antisymmetric-leq-Finitely-Graded-Subposet :
    (x y : element-Finitely-Graded-Subposet) →
    leq-Finitely-Graded-Subposet x y → leq-Finitely-Graded-Subposet y x → Id x y
  antisymmetric-leq-Finitely-Graded-Subposet x y H K =
    is-injective-map-emb-element-Finitely-Graded-Subposet
      ( antisymmetric-leq-Finitely-Graded-Poset X
        ( map-emb-element-Finitely-Graded-Subposet x)
        ( map-emb-element-Finitely-Graded-Subposet y)
        ( H)
        ( K))

  poset-Finitely-Graded-Subposet : Poset (l1 ⊔ l3) (l1 ⊔ l2)
  pr1 poset-Finitely-Graded-Subposet = element-Finitely-Graded-Subposet
  pr1 (pr2 poset-Finitely-Graded-Subposet) = leq-finitely-graded-subposet-Prop
  pr1 (pr1 (pr2 (pr2 poset-Finitely-Graded-Subposet))) =
    refl-leq-Finitely-Graded-Subposet
  pr2 (pr1 (pr2 (pr2 poset-Finitely-Graded-Subposet))) =
    transitive-leq-Finitely-Graded-Subposet
  pr2 (pr2 (pr2 poset-Finitely-Graded-Subposet)) =
    antisymmetric-leq-Finitely-Graded-Subposet
```

### Inclusion of finitely graded subposets

```agda

module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    {l3 l4 : Level}
    (S : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3)
    (T : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l4)
    where

    inclusion-finitely-graded-subposet-Prop : Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-finitely-graded-subposet-Prop =
      Π-Prop
        ( Fin (succ-ℕ k))
        ( λ i →
          Π-Prop
            ( face-Finitely-Graded-Poset X i)
            ( λ x → hom-Prop (S x) (T x)))

    inclusion-Finitely-Graded-Subposet : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-Finitely-Graded-Subposet =
      type-Prop inclusion-finitely-graded-subposet-Prop

    is-prop-inclusion-Finitely-Graded-Subposet :
      is-prop inclusion-Finitely-Graded-Subposet
    is-prop-inclusion-Finitely-Graded-Subposet =
      is-prop-type-Prop inclusion-finitely-graded-subposet-Prop

  refl-inclusion-Finitely-Graded-Subposet :
    {l3 : Level}
    (S : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3) →
    inclusion-Finitely-Graded-Subposet S S
  refl-inclusion-Finitely-Graded-Subposet S i x = id

  transitive-inclusion-Finitely-Graded-Subposet :
    {l3 l4 l5 : Level}
    (S : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3)
    (T : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l4)
    (U : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l5) →
    inclusion-Finitely-Graded-Subposet T U →
    inclusion-Finitely-Graded-Subposet S T →
    inclusion-Finitely-Graded-Subposet S U
  transitive-inclusion-Finitely-Graded-Subposet S T U g f i x =
    (g i x) ∘ (f i x)

  finitely-graded-subposet-Preorder :
    (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  pr1 (finitely-graded-subposet-Preorder l) =
    {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l
  pr1 (pr2 (finitely-graded-subposet-Preorder l)) =
    inclusion-finitely-graded-subposet-Prop
  pr1 (pr2 (pr2 (finitely-graded-subposet-Preorder l))) =
    refl-inclusion-Finitely-Graded-Subposet
  pr2 (pr2 (pr2 (finitely-graded-subposet-Preorder l))) =
    transitive-inclusion-Finitely-Graded-Subposet
```

### Chains in finitely graded posets

```agda

module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    {l3 : Level}
    (S : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3)
    where

    is-chain-finitely-graded-subposet-Prop : Prop (l1 ⊔ l2 ⊔ l3)
    is-chain-finitely-graded-subposet-Prop =
      is-total-poset-Prop (poset-Finitely-Graded-Subposet X S)

    is-chain-Finitely-Graded-Subposet : UU (l1 ⊔ l2 ⊔ l3)
    is-chain-Finitely-Graded-Subposet =
      type-Prop is-chain-finitely-graded-subposet-Prop

    is-prop-is-chain-Finitely-Graded-Subposet :
      is-prop is-chain-Finitely-Graded-Subposet
    is-prop-is-chain-Finitely-Graded-Subposet =
      is-prop-type-Prop is-chain-finitely-graded-subposet-Prop

  chain-Finitely-Graded-Poset : (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  chain-Finitely-Graded-Poset l = Σ _ (is-chain-Finitely-Graded-Subposet {l})

  module _
    {l : Level} (C : chain-Finitely-Graded-Poset l)
    where

    subtype-chain-Finitely-Graded-Poset :
      {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l
    subtype-chain-Finitely-Graded-Poset = pr1 C

module _
  {l1 l2 l3 l4 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  (C : chain-Finitely-Graded-Poset X l3) (D : chain-Finitely-Graded-Poset X l4)
  where

  inclusion-chain-finitely-graded-poset-Prop : Prop (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-finitely-graded-poset-Prop =
    inclusion-finitely-graded-subposet-Prop X
      ( subtype-chain-Finitely-Graded-Poset X C)
      ( subtype-chain-Finitely-Graded-Poset X D)

  inclusion-chain-Finitely-Graded-Poset : UU (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-Finitely-Graded-Poset =
    inclusion-Finitely-Graded-Subposet X
      ( subtype-chain-Finitely-Graded-Poset X C)
      ( subtype-chain-Finitely-Graded-Poset X D)

  is-prop-inclusion-chain-Finitely-Graded-Poset :
    is-prop inclusion-chain-Finitely-Graded-Poset
  is-prop-inclusion-chain-Finitely-Graded-Poset =
    is-prop-inclusion-Finitely-Graded-Subposet X
      ( subtype-chain-Finitely-Graded-Poset X C)
      ( subtype-chain-Finitely-Graded-Poset X D)
```

### Maximal chains in preorders

```agda

module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    {l3 : Level} (C : chain-Finitely-Graded-Poset X l3)
    where

    is-maximal-chain-finitely-graded-poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
    is-maximal-chain-finitely-graded-poset-Prop =
      Π-Prop
        ( chain-Finitely-Graded-Poset X l3)
        ( λ D → inclusion-chain-finitely-graded-poset-Prop X D C)

    is-maximal-chain-Finitely-Graded-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
    is-maximal-chain-Finitely-Graded-Poset =
      type-Prop is-maximal-chain-finitely-graded-poset-Prop

    is-prop-is-maximal-chain-Finitely-Graded-Poset :
      is-prop is-maximal-chain-Finitely-Graded-Poset
    is-prop-is-maximal-chain-Finitely-Graded-Poset =
      is-prop-type-Prop is-maximal-chain-finitely-graded-poset-Prop

  maximal-chain-Finitely-Graded-Poset :
    (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  maximal-chain-Finitely-Graded-Poset l =
    Σ _ (is-maximal-chain-Finitely-Graded-Poset {l})

  module _
    {l3 : Level} (C : maximal-chain-Finitely-Graded-Poset l3)
    where

    chain-maximal-chain-Finitely-Graded-Poset :
      chain-Finitely-Graded-Poset X l3
    chain-maximal-chain-Finitely-Graded-Poset = pr1 C

    is-maximal-chain-maximal-chain-Finitely-Graded-Poset :
      is-maximal-chain-Finitely-Graded-Poset
        chain-maximal-chain-Finitely-Graded-Poset
    is-maximal-chain-maximal-chain-Finitely-Graded-Poset = pr2 C

    subtype-maximal-chain-Finitely-Graded-Poset :
      {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3
    subtype-maximal-chain-Finitely-Graded-Poset =
      subtype-chain-Finitely-Graded-Poset X
        chain-maximal-chain-Finitely-Graded-Poset
