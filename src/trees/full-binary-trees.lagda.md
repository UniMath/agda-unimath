# Full binary trees

```agda
module trees.full-binary-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

A
{{#concept "full binary tree" Agda=full-binary-tree WD="full binary tree" WDID=Q29791667}}
is a finite [directed tree](trees.directed-trees.md) in which every non-leaf
node has a specified left branch and a specified right branch. More precisely, a
full binary tree consists of a root, a left full binary subtree and a right full
binary subtree.

## Definitions

### Full binary trees

```agda
data full-binary-tree : UU lzero where
  leaf-full-binary-tree : full-binary-tree
  join-full-binary-tree : (s t : full-binary-tree) → full-binary-tree
```

### The nodes of a full binary tree

```agda
node-full-binary-tree : full-binary-tree → UU lzero
node-full-binary-tree leaf-full-binary-tree = unit
node-full-binary-tree (join-full-binary-tree G H) =
  node-full-binary-tree G + node-full-binary-tree H
```

### The weight of a full binary tree

This counts the number of nodes in `T : full-binary-tree` and can be thought of
as an arboreal version of the length of a [list](lists.lists.md).

```agda
weight-full-binary-tree : full-binary-tree → ℕ
weight-full-binary-tree leaf-full-binary-tree = 1
weight-full-binary-tree (join-full-binary-tree T U) =
  weight-full-binary-tree T +ℕ weight-full-binary-tree U
```

### Characterizing the identity type of full binary trees

```agda
Eq-full-binary-tree : full-binary-tree → full-binary-tree → UU lzero
Eq-full-binary-tree leaf-full-binary-tree leaf-full-binary-tree = unit
Eq-full-binary-tree leaf-full-binary-tree (join-full-binary-tree V V₁) = empty
Eq-full-binary-tree (join-full-binary-tree U U₁) leaf-full-binary-tree = empty
Eq-full-binary-tree (join-full-binary-tree U U₁) (join-full-binary-tree V V₁) =
  Eq-full-binary-tree U V × Eq-full-binary-tree U₁ V₁

is-prop-Eq-full-binary-tree :
  (U V : full-binary-tree) → is-prop (Eq-full-binary-tree U V)
is-prop-Eq-full-binary-tree leaf-full-binary-tree leaf-full-binary-tree =
  is-prop-unit
is-prop-Eq-full-binary-tree leaf-full-binary-tree (join-full-binary-tree V V₁) =
  is-prop-empty
is-prop-Eq-full-binary-tree (join-full-binary-tree U U₁) leaf-full-binary-tree =
  is-prop-empty
is-prop-Eq-full-binary-tree
  (join-full-binary-tree U U₁) (join-full-binary-tree V V₁) =
    is-prop-product
    ( is-prop-Eq-full-binary-tree U V)
    ( is-prop-Eq-full-binary-tree U₁ V₁)

refl-Eq-full-binary-tree : (U : full-binary-tree) → Eq-full-binary-tree U U
refl-Eq-full-binary-tree leaf-full-binary-tree = star
refl-Eq-full-binary-tree (join-full-binary-tree U U₁) =
  refl-Eq-full-binary-tree U , refl-Eq-full-binary-tree U₁

Eq-eq-full-binary-tree :
  {U V : full-binary-tree} → U ＝ V → Eq-full-binary-tree U V
Eq-eq-full-binary-tree {U} refl = refl-Eq-full-binary-tree U

eq-Eq-full-binary-tree :
  (U V : full-binary-tree) → Eq-full-binary-tree U V → U ＝ V
eq-Eq-full-binary-tree leaf-full-binary-tree leaf-full-binary-tree _ = refl
eq-Eq-full-binary-tree leaf-full-binary-tree (join-full-binary-tree V V₁) ()
eq-Eq-full-binary-tree (join-full-binary-tree U U₁) leaf-full-binary-tree ()
eq-Eq-full-binary-tree
  (join-full-binary-tree U U₁) (join-full-binary-tree V V₁) (p , q) =
  ap-binary join-full-binary-tree
    ( eq-Eq-full-binary-tree U V p)
    ( eq-Eq-full-binary-tree U₁ V₁ q)

map-total-Eq-full-binary-tree :
  (U V : full-binary-tree) →
  Σ full-binary-tree (Eq-full-binary-tree U) →
  Σ full-binary-tree (Eq-full-binary-tree V) →
  Σ full-binary-tree (Eq-full-binary-tree (join-full-binary-tree U V))
pr1 (map-total-Eq-full-binary-tree U V (W , p) (X , q)) =
  join-full-binary-tree W X
pr1 (pr2 (map-total-Eq-full-binary-tree U V (W , p) (X , q))) = p
pr2 (pr2 (map-total-Eq-full-binary-tree U V (W , p) (X , q))) = q

is-torsorial-Eq-full-binary-tree :
  (T : full-binary-tree) → is-torsorial (Eq-full-binary-tree T)
pr1 (is-torsorial-Eq-full-binary-tree T) = T , refl-Eq-full-binary-tree T
pr2 (is-torsorial-Eq-full-binary-tree leaf-full-binary-tree)
  (leaf-full-binary-tree , star) = refl
pr2 (is-torsorial-Eq-full-binary-tree leaf-full-binary-tree)
  (join-full-binary-tree U U₁ , ())
pr2 (is-torsorial-Eq-full-binary-tree (join-full-binary-tree T T₁))
  (leaf-full-binary-tree , ())
pr2 (is-torsorial-Eq-full-binary-tree (join-full-binary-tree T T₁))
  (join-full-binary-tree U U₁ , p , q) =
    ap-binary (map-total-Eq-full-binary-tree T T₁)
    ( pr2 (is-torsorial-Eq-full-binary-tree T) (U , p))
    ( pr2 (is-torsorial-Eq-full-binary-tree T₁) (U₁ , q))

is-equiv-Eq-eq-full-binary-tree :
  {U V : full-binary-tree} → is-equiv (Eq-eq-full-binary-tree {U} {V})
is-equiv-Eq-eq-full-binary-tree {U} {V} =
  fundamental-theorem-id
  ( is-torsorial-Eq-full-binary-tree U)
  ( λ T p → Eq-eq-full-binary-tree p)
  ( V)
```

### The type of full binary trees has decidable equality

```agda
is-decidable-Eq-full-binary-tree :
  (U V : full-binary-tree) → is-decidable (Eq-full-binary-tree U V)
is-decidable-Eq-full-binary-tree leaf-full-binary-tree leaf-full-binary-tree =
  inl star
is-decidable-Eq-full-binary-tree
  leaf-full-binary-tree (join-full-binary-tree V V₁) =
    inr (λ ())
is-decidable-Eq-full-binary-tree
  (join-full-binary-tree U U₁) leaf-full-binary-tree =
    inr (λ ())
is-decidable-Eq-full-binary-tree (join-full-binary-tree U U₁) (join-full-binary-tree V V₁) with is-decidable-Eq-full-binary-tree U V | is-decidable-Eq-full-binary-tree U₁ V₁
... | inl p | inl q = inl (pair p q)
... | inl p | inr q = inr (λ z → q (pr2 z))
... | inr p | inl q = inr (λ z → p (pr1 z))
... | inr p | inr q = inr (λ z → p (pr1 z))

has-decidable-equality-full-binary-tree :
  has-decidable-equality full-binary-tree
has-decidable-equality-full-binary-tree U V =
  is-decidable-iff
  ( eq-Eq-full-binary-tree U V)
  ( Eq-eq-full-binary-tree)
  ( is-decidable-Eq-full-binary-tree U V)

is-set-full-binary-tree : is-set full-binary-tree
is-set-full-binary-tree =
  is-set-has-decidable-equality has-decidable-equality-full-binary-tree

full-binary-tree-Set : Set lzero
pr1 full-binary-tree-Set = full-binary-tree
pr2 full-binary-tree-Set = is-set-full-binary-tree
```
