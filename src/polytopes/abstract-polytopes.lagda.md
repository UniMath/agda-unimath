# Abstract polytopes

```agda
module polytopes.abstract-polytopes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.finitely-graded-posets
open import order-theory.posets

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define
{{#concept "abstract polytopes" WD="abstract polytope" WDID=Q4669958 Agda=Polytope}}
as [finitely graded posets](order-theory.finitely-graded-posets.md) satisfying
certain axioms. In the classical definition, the grading is a consequence of the
axioms. Here, we take finitely graded posets as our starting point.

The first axiom of polytopes asserts that polytopes have a least and a largest
element. This is already defined as
`least-and-largest-element-finitely-graded-poset-Prop`.

Next, we assert the
{{#concept "diamond condition" Disambiguation="for abstract polytopes" Agda=diamond-condition-Finitely-Graded-Poset}}
for abstract polytopes.

## Definition

### The diamond condition

```agda
diamond-condition-finitely-graded-poset-Prop :
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k) →
  Prop (l1 ⊔ l2)
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
              ( succ-Fin
                ( succ-ℕ (succ-ℕ k))
                ( succ-Fin
                  ( succ-ℕ (succ-ℕ k))
                  ( inl-Fin (succ-ℕ k) (inl-Fin k i)))))
            ( λ y →
              has-cardinality-ℕ-Prop 2
                ( Σ ( face-Finitely-Graded-Poset X
                      ( succ-Fin
                        ( succ-ℕ (succ-ℕ k))
                        ( inl-Fin (succ-ℕ k) (inl-Fin k i))))
                    ( λ z →
                      adjacent-Finitely-Graded-Poset X (inl-Fin k i) x z ×
                      adjacent-Finitely-Graded-Poset X
                        ( succ-Fin (succ-ℕ k) (inl-Fin k i))
                        ( z)
                        ( y))))))

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

### Prepolytopes

We introduce the notion of prepolytopes to be finitely graded posets equipped
with a least and a largest element, and satisfying the diamond condition. Before
we state the remaining conditions of polytopes, we introduce some terminology

```agda
Prepolytope : (l1 l2 : Level) (k : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
Prepolytope l1 l2 k =
  Σ ( Finitely-Graded-Poset l1 l2 k)
    ( λ X →
      has-bottom-and-top-element-Finitely-Graded-Poset X ×
      diamond-condition-Finitely-Graded-Poset X)
```

## Properties

### Basic structure of prepolytopes

```agda
module _
  {l1 l2 : Level} {k : ℕ} (X : Prepolytope l1 l2 k)
  where

  finitely-graded-poset-Prepolytope : Finitely-Graded-Poset l1 l2 k
  finitely-graded-poset-Prepolytope = pr1 X

  has-bottom-and-top-element-Prepolytope :
    has-bottom-and-top-element-Finitely-Graded-Poset
      finitely-graded-poset-Prepolytope
  has-bottom-and-top-element-Prepolytope = pr1 (pr2 X)

  has-bottom-element-Prepolytope :
    has-bottom-element-Finitely-Graded-Poset finitely-graded-poset-Prepolytope
  has-bottom-element-Prepolytope = pr1 has-bottom-and-top-element-Prepolytope

  has-top-element-Prepolytope :
    has-top-element-Finitely-Graded-Poset finitely-graded-poset-Prepolytope
  has-top-element-Prepolytope = pr2 has-bottom-and-top-element-Prepolytope

  diamond-condition-Prepolytope :
    diamond-condition-Finitely-Graded-Poset finitely-graded-poset-Prepolytope
  diamond-condition-Prepolytope = pr2 (pr2 X)

  module _
    (i : Fin (succ-ℕ k))
    where

    face-prepolytope-Set : Set l1
    face-prepolytope-Set =
      face-Finitely-Graded-Poset-Set finitely-graded-poset-Prepolytope i

    face-Prepolytope : UU l1
    face-Prepolytope =
      face-Finitely-Graded-Poset finitely-graded-poset-Prepolytope i

    is-set-face-Prepolytope : is-set face-Prepolytope
    is-set-face-Prepolytope =
      is-set-face-Finitely-Graded-Poset finitely-graded-poset-Prepolytope i

  module _
    (i : Fin k) (y : face-Prepolytope (inl-Fin k i))
    (z : face-Prepolytope (succ-Fin (succ-ℕ k) (inl-Fin k i)))
    where

    adjancent-prepolytope-Prop : Prop l2
    adjancent-prepolytope-Prop =
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

  set-Prepolytope : Set l1
  set-Prepolytope =
    set-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  type-Prepolytope : UU l1
  type-Prepolytope =
    type-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  is-set-type-Prepolytope : is-set type-Prepolytope
  is-set-type-Prepolytope =
    is-set-type-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  element-face-Prepolytope :
    {i : Fin (succ-ℕ k)} → face-Prepolytope i → type-Prepolytope
  element-face-Prepolytope =
    element-face-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  shape-Prepolytope :
    type-Prepolytope → Fin (succ-ℕ k)
  shape-Prepolytope =
    shape-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  face-element-Prepolytope :
    (x : type-Prepolytope) → face-Prepolytope (shape-Prepolytope x)
  face-element-Prepolytope =
    face-type-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  path-faces-Prepolytope :
    {i j : Fin (succ-ℕ k)} →
    face-Prepolytope i → face-Prepolytope j → UU (l1 ⊔ l2)
  path-faces-Prepolytope x y =
    path-faces-Finitely-Graded-Poset finitely-graded-poset-Prepolytope x y

  refl-path-faces-Prepolytope :
    {i : Fin (succ-ℕ k)} (x : face-Prepolytope i) → path-faces-Prepolytope x x
  refl-path-faces-Prepolytope x = refl-path-faces-Finitely-Graded-Poset

  cons-path-faces-Prepolytope :
    {i : Fin (succ-ℕ k)} {x : face-Prepolytope i}
    {j : Fin k} {y : face-Prepolytope (inl-Fin k j)}
    {z : face-Prepolytope (succ-Fin (succ-ℕ k) (inl-Fin k j))} →
    adjacent-Prepolytope j y z → path-faces-Prepolytope x y →
    path-faces-Prepolytope x z
  cons-path-faces-Prepolytope a p = cons-path-faces-Finitely-Graded-Poset a p

  tr-refl-path-faces-Preposet :
    {i j : Fin (succ-ℕ k)} (p : j ＝ i) (x : face-Prepolytope j) →
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

  path-elements-Prepolytope : (x y : type-Prepolytope) → UU (l1 ⊔ l2)
  path-elements-Prepolytope =
    path-elements-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  refl-path-elements-Prepolytope :
    (x : type-Prepolytope) → path-elements-Prepolytope x x
  refl-path-elements-Prepolytope =
    refl-path-elements-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  concat-path-elements-Prepolytope :
    (x y z : type-Prepolytope) →
    path-elements-Prepolytope y z → path-elements-Prepolytope x y →
    path-elements-Prepolytope x z
  concat-path-elements-Prepolytope =
    concat-path-elements-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  leq-type-path-faces-Prepolytope :
    {i1 i2 : Fin (succ-ℕ k)} (x : face-Prepolytope i1)
    (y : face-Prepolytope i2) →
    path-faces-Prepolytope x y → leq-Fin (succ-ℕ k) i1 i2
  leq-type-path-faces-Prepolytope =
    leq-type-path-faces-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  eq-path-elements-Prepolytope :
    (x y : type-Prepolytope)
    (p : shape-Prepolytope x ＝ shape-Prepolytope y) →
    path-elements-Prepolytope x y → x ＝ y
  eq-path-elements-Prepolytope =
    eq-path-elements-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  eq-path-faces-Prepolytope :
    {i : Fin (succ-ℕ k)} (x y : face-Prepolytope i) →
    path-faces-Prepolytope x y → x ＝ y
  eq-path-faces-Prepolytope =
    eq-path-faces-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  antisymmetric-path-elements-Prepolytope :
    (x y : type-Prepolytope) → path-elements-Prepolytope x y →
    path-elements-Prepolytope y x → x ＝ y
  antisymmetric-path-elements-Prepolytope =
    antisymmetric-path-elements-Finitely-Graded-Poset
      finitely-graded-poset-Prepolytope

  module _
    (x y : type-Prepolytope)
    where

    leq-prepolytope-Prop : Prop (l1 ⊔ l2)
    leq-prepolytope-Prop =
      leq-Finitely-Graded-Poset-Prop finitely-graded-poset-Prepolytope x y

    leq-Prepolytope : UU (l1 ⊔ l2)
    leq-Prepolytope =
      leq-Finitely-Graded-Poset finitely-graded-poset-Prepolytope x y

    is-prop-leq-Prepolytope : is-prop leq-Prepolytope
    is-prop-leq-Prepolytope =
      is-prop-leq-Finitely-Graded-Poset finitely-graded-poset-Prepolytope x y

  refl-leq-Prepolytope : is-reflexive leq-Prepolytope
  refl-leq-Prepolytope =
    refl-leq-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  transitive-leq-Prepolytope : is-transitive leq-Prepolytope
  transitive-leq-Prepolytope =
    transitive-leq-Finitely-Graded-Poset finitely-graded-poset-Prepolytope

  antisymmetric-leq-Prepolytope : is-antisymmetric leq-Prepolytope
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
    {i : Fin (succ-ℕ k)} → face-Prepolytope i → Prop l
  subtype-flag-Prepolytope =
    subtype-maximal-chain-Finitely-Graded-Poset
      finitely-graded-poset-Prepolytope

  type-subtype-flag-Prepolytope :
    {l : Level} (F : flag-Prepolytope l) →
    {i : Fin (succ-ℕ k)} → face-Prepolytope i → UU l
  type-subtype-flag-Prepolytope F x =
    type-Prop (subtype-flag-Prepolytope F x)

  face-flag-Prepolytope :
    {l : Level} (F : flag-Prepolytope l) → Fin (succ-ℕ k) → UU (l1 ⊔ l)
  face-flag-Prepolytope F i =
    Σ (face-Prepolytope i) (type-subtype-flag-Prepolytope F)

  face-bottom-element-Prepolytope : face-Prepolytope (zero-Fin k)
  face-bottom-element-Prepolytope = pr1 has-bottom-element-Prepolytope

  element-bottom-element-Prepolytope : type-Prepolytope
  element-bottom-element-Prepolytope =
    element-face-Prepolytope face-bottom-element-Prepolytope

  is-bottom-element-bottom-element-Prepolytope :
    (x : type-Prepolytope) →
    leq-Prepolytope element-bottom-element-Prepolytope x
  is-bottom-element-bottom-element-Prepolytope =
    pr2 has-bottom-element-Prepolytope

  face-has-top-element-Prepolytope : face-Prepolytope (neg-one-Fin k)
  face-has-top-element-Prepolytope = pr1 has-top-element-Prepolytope

  element-has-top-element-Prepolytope : type-Prepolytope
  element-has-top-element-Prepolytope =
    element-face-Prepolytope face-has-top-element-Prepolytope

  is-has-top-element-has-top-element-Prepolytope :
    (x : type-Prepolytope) →
    leq-Prepolytope x element-has-top-element-Prepolytope
  is-has-top-element-has-top-element-Prepolytope =
    pr2 has-top-element-Prepolytope

  is-contr-face-bottom-dimension-Prepolytope :
    is-contr (face-Prepolytope (zero-Fin k))
  pr1 is-contr-face-bottom-dimension-Prepolytope =
    face-bottom-element-Prepolytope
  pr2 is-contr-face-bottom-dimension-Prepolytope x =
    apply-universal-property-trunc-Prop
      ( is-bottom-element-bottom-element-Prepolytope
        ( element-face-Prepolytope x))
      ( Id-Prop
        ( face-prepolytope-Set (zero-Fin k))
        ( face-bottom-element-Prepolytope)
        ( x))
      ( λ p → eq-path-faces-Prepolytope face-bottom-element-Prepolytope x p)

  is-contr-face-top-dimension-Prepolytope :
    is-contr (face-Prepolytope (neg-one-Fin k))
  pr1 is-contr-face-top-dimension-Prepolytope =
    face-has-top-element-Prepolytope
  pr2 is-contr-face-top-dimension-Prepolytope x =
    apply-universal-property-trunc-Prop
      ( is-has-top-element-has-top-element-Prepolytope
        ( element-face-Prepolytope x))
      ( Id-Prop
        ( face-prepolytope-Set (neg-one-Fin k))
        ( face-has-top-element-Prepolytope)
        ( x))
      ( λ p →
        inv (eq-path-faces-Prepolytope x face-has-top-element-Prepolytope p))
```

### Flags are equivalently described as paths from the least to the largest element

```agda
  is-on-path-face-prepolytope-Prop :
    {i1 i2 : Fin (succ-ℕ k)} {x : face-Prepolytope i1} {y : face-Prepolytope i2}
    (p : path-faces-Prepolytope x y) →
    {i3 : Fin (succ-ℕ k)} → face-Prepolytope i3 → Prop l1
  is-on-path-face-prepolytope-Prop
    {x = x} refl-path-faces-Finitely-Graded-Poset z =
    Id-Prop
      ( set-Prepolytope)
      ( element-face-Prepolytope x)
      ( element-face-Prepolytope z)
  is-on-path-face-prepolytope-Prop
    ( cons-path-faces-Finitely-Graded-Poset {z = w} a p) z =
    disjunction-Prop
      ( is-on-path-face-prepolytope-Prop p z)
      ( Id-Prop
        ( set-Prepolytope)
        ( element-face-Prepolytope w)
        ( element-face-Prepolytope z))

  module _
    {i1 i2 i3 : Fin (succ-ℕ k)}
    {x : face-Prepolytope i1} {y : face-Prepolytope i2}
    where

    is-on-path-face-Prepolytope :
      path-faces-Prepolytope x y → face-Prepolytope i3 → UU l1
    is-on-path-face-Prepolytope p z =
      type-Prop (is-on-path-face-prepolytope-Prop p z)

    is-prop-is-on-path-face-Prepolytope :
      (p : path-faces-Prepolytope x y) (z : face-Prepolytope i3) →
      is-prop (is-on-path-face-Prepolytope p z)
    is-prop-is-on-path-face-Prepolytope p z =
      is-prop-type-Prop (is-on-path-face-prepolytope-Prop p z)
```

### Proof condition P2 of polytopes

The second axiom of polytopes asserts that every maximal chain has k elements.
Note that every maximal chain is a path from the bottom element to the top
element, which necessarily passes through all dimensions. Therefore, the second
axiom follows from our setup. Note that we didn't start with general posets, but
with finitely graded posets.

```agda
module _
  {l1 l2 : Level} (l : Level) {k : ℕ} (X : Prepolytope l1 l2 k)
  where

  condition-P2-prepolytope-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l)
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

### Strong connectedness of polytopes

The strong connectedness condition for polytopes asserts that the unordered
graph of flags of a polytope is connected. The edges in this graph are punctured
flags, i.e., chains that have exactly one element in each dimension except in
one dimension that is neither the top nor the bottom dimension. A punctured flag
connects the two flags it is a subchain of.

### The definition of polytopes

```agda
Polytope :
  (l1 l2 l3 : Level) (k : ℕ) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Polytope l1 l2 l3 k =
  Σ ( Prepolytope l1 l2 k)
    ( λ X →
      ( condition-P2-Prepolytope l3 X) ×
      unit)
```
