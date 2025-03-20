# Transitive higher group actions

```agda
open import foundation.function-extensionality-axiom

module
  higher-group-theory.transitive-higher-group-actions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types funext
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.inhabited-types funext
open import foundation.propositional-truncations funext
open import foundation.propositions funext
open import foundation.regensburg-extension-fundamental-theorem-of-identity-types funext
open import foundation.surjective-maps funext
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import higher-group-theory.higher-group-actions funext
open import higher-group-theory.higher-groups funext
open import higher-group-theory.orbits-higher-group-actions funext
```

</details>

## Idea

Consider an [∞-group](higher-group-theory.higher-groups.md) `G` and an
[∞-group action](higher-group-theory.higher-group-actions.md) of `G` on `X`. We
say that `X` is **transitive** if its type of
[orbits](higher-group-theory.orbits-higher-group-actions.md) is
[connected](foundation.connected-types.md).

[Equivalently](foundation.logical-equivalences.md), we say that `X` is
**abstractly transitive** if the underlying type of `X` is
[inhabited](foundation.inhabited-types.md) and for any element `x : X (sh G)` of
the underlying type of `X` the action map

```text
  g ↦ mul-action-∞-Group G X g x
```

is [surjective](foundation.surjective-maps.md). The equivalence of these two
conditions is established via the
[Regensburg extension of the fundamental theorem of identity types](foundation.regensburg-extension-fundamental-theorem-of-identity-types.md).

Note that it is necessary to include the condition that `X` is inhabited in the
condition that `G` acts transitively on `X`. A first reason is that this makes
the condition of being abstractly transitive equivalent to the condition of
being transitive. A second reason is that this way we will be able to recover
the familiar property that a `G`-action `X` is a `G`-torsor if and only if it is
both [free](higher-group-theory.free-higher-group-actions.md) and transitive.

## Definitions

### The predicate of being a transitive higher group action

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  is-transitive-prop-action-∞-Group : Prop (l1 ⊔ l2)
  is-transitive-prop-action-∞-Group =
    is-0-connected-Prop (orbit-action-∞-Group G X)

  is-transitive-action-∞-Group : UU (l1 ⊔ l2)
  is-transitive-action-∞-Group = type-Prop is-transitive-prop-action-∞-Group

  is-prop-is-transitive-action-∞-Group : is-prop is-transitive-action-∞-Group
  is-prop-is-transitive-action-∞-Group =
    is-prop-type-Prop is-transitive-prop-action-∞-Group
```

### The predicate of being an abstractly transitive higher group action

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  is-abstractly-transitive-prop-action-∞-Group : Prop (l1 ⊔ l2)
  is-abstractly-transitive-prop-action-∞-Group =
    product-Prop
      ( is-inhabited-Prop (type-action-∞-Group G X))
      ( Π-Prop
        ( type-action-∞-Group G X)
        ( λ x → is-surjective-Prop (λ g → mul-action-∞-Group G X g x)))

  is-abstractly-transitive-action-∞-Group : UU (l1 ⊔ l2)
  is-abstractly-transitive-action-∞-Group =
    type-Prop is-abstractly-transitive-prop-action-∞-Group

  is-prop-is-abstractly-transitive-action-∞-Group :
    is-prop is-abstractly-transitive-action-∞-Group
  is-prop-is-abstractly-transitive-action-∞-Group =
    is-prop-type-Prop is-abstractly-transitive-prop-action-∞-Group
```

### Transitive higher group actions

```agda
transitive-action-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) → UU (l1 ⊔ lsuc l2)
transitive-action-∞-Group l2 G =
  Σ (action-∞-Group l2 G) (is-transitive-action-∞-Group G)

module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : transitive-action-∞-Group l2 G)
  where

  action-transitive-action-∞-Group : action-∞-Group l2 G
  action-transitive-action-∞-Group = pr1 X

  is-transitive-transitive-action-∞-Group :
    is-transitive-action-∞-Group G action-transitive-action-∞-Group
  is-transitive-transitive-action-∞-Group = pr2 X

  type-transitive-action-∞-Group : UU l2
  type-transitive-action-∞-Group =
    type-action-∞-Group G action-transitive-action-∞-Group

  mul-transitive-action-∞-Group :
    type-∞-Group G →
    type-transitive-action-∞-Group → type-transitive-action-∞-Group
  mul-transitive-action-∞-Group =
    mul-action-∞-Group G action-transitive-action-∞-Group

  associative-mul-transitive-action-∞-Group :
    (g h : type-∞-Group G) (x : type-transitive-action-∞-Group) →
    mul-transitive-action-∞-Group (mul-∞-Group G g h) x ＝
    mul-transitive-action-∞-Group h (mul-transitive-action-∞-Group g x)
  associative-mul-transitive-action-∞-Group =
    associative-mul-action-∞-Group G action-transitive-action-∞-Group

  unit-law-mul-transitive-action-∞-Group :
    (x : type-transitive-action-∞-Group) →
    mul-transitive-action-∞-Group (unit-∞-Group G) x ＝ x
  unit-law-mul-transitive-action-∞-Group =
    unit-law-mul-action-∞-Group G action-transitive-action-∞-Group
```

## Properties

### If an action is abstractly transitive, then transport is surjective

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  abstract
    is-surjective-tr-is-abstractly-transitive-action-∞-Group :
      is-abstractly-transitive-action-∞-Group G X →
      (u : classifying-type-∞-Group G)
      (x : X (shape-∞-Group G)) →
      is-surjective (λ (p : shape-∞-Group G ＝ u) → tr X p x)
    is-surjective-tr-is-abstractly-transitive-action-∞-Group H u x =
      apply-universal-property-trunc-Prop
        ( mere-eq-classifying-type-∞-Group G (shape-∞-Group G) u)
        ( is-surjective-Prop _)
        ( λ where refl → pr2 H x)
```

### An action is transitive if and only if it is abstractly transitive

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  is-transitive-is-abstractly-transitive-action-∞-Group :
    is-abstractly-transitive-action-∞-Group G X →
    is-transitive-action-∞-Group G X
  is-transitive-is-abstractly-transitive-action-∞-Group (H , K) =
    forward-implication-extended-fundamental-theorem-id-surjective
      ( shape-∞-Group G)
      ( is-0-connected-classifying-type-∞-Group G)
      ( λ f u →
        is-surjective-htpy
          ( compute-map-out-of-identity-type f u)
          ( is-surjective-tr-is-abstractly-transitive-action-∞-Group G X
            ( H , K)
            ( u)
            ( f (shape-∞-Group G) refl)))
      ( H)

  abstract
    is-inhabited-is-transitive-action-∞-Group :
      is-transitive-action-∞-Group G X → is-inhabited (type-action-∞-Group G X)
    is-inhabited-is-transitive-action-∞-Group H =
      apply-universal-property-trunc-Prop
        ( is-inhabited-is-0-connected H)
        ( is-inhabited-Prop _)
        ( λ (u , x) →
          apply-universal-property-trunc-Prop
            ( mere-eq-classifying-type-∞-Group G (shape-∞-Group G) u)
            ( is-inhabited-Prop _)
            ( λ where refl → unit-trunc-Prop x))

  is-surjective-mul-right-is-transitive-action-∞-Group :
    is-transitive-action-∞-Group G X →
    (x : type-action-∞-Group G X) →
    is-surjective (λ g → mul-action-∞-Group G X g x)
  is-surjective-mul-right-is-transitive-action-∞-Group H x =
    backward-implication-extended-fundamental-theorem-id-surjective
      ( shape-∞-Group G)
      ( H)
      ( λ u p → tr X p x)
      ( shape-∞-Group G)

  is-abstractly-transitive-is-transitive-action-∞-Group :
    is-transitive-action-∞-Group G X →
    is-abstractly-transitive-action-∞-Group G X
  pr1 (is-abstractly-transitive-is-transitive-action-∞-Group H) =
    is-inhabited-is-transitive-action-∞-Group H
  pr2 (is-abstractly-transitive-is-transitive-action-∞-Group H) =
    is-surjective-mul-right-is-transitive-action-∞-Group H

module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : transitive-action-∞-Group l2 G)
  where

  is-inhabited-transitive-action-∞-Group :
    is-inhabited (type-transitive-action-∞-Group G X)
  is-inhabited-transitive-action-∞-Group =
    is-inhabited-is-transitive-action-∞-Group G
      ( action-transitive-action-∞-Group G X)
      ( is-transitive-transitive-action-∞-Group G X)

  inhabited-type-transitive-action-∞-Group :
    Inhabited-Type l2
  pr1 inhabited-type-transitive-action-∞-Group =
    type-transitive-action-∞-Group G X
  pr2 inhabited-type-transitive-action-∞-Group =
    is-inhabited-transitive-action-∞-Group

  is-abstractly-transitive-transitive-action-∞-Group :
    is-abstractly-transitive-action-∞-Group G
      ( action-transitive-action-∞-Group G X)
  is-abstractly-transitive-transitive-action-∞-Group =
    is-abstractly-transitive-is-transitive-action-∞-Group G
      ( action-transitive-action-∞-Group G X)
      ( is-transitive-transitive-action-∞-Group G X)

  is-surjective-tr-transitive-action-∞-Group :
    (u : classifying-type-∞-Group G) (x : type-transitive-action-∞-Group G X) →
    is-surjective
      ( λ (p : shape-∞-Group G ＝ u) →
        tr (action-transitive-action-∞-Group G X) p x)
  is-surjective-tr-transitive-action-∞-Group =
    is-surjective-tr-is-abstractly-transitive-action-∞-Group G
      ( action-transitive-action-∞-Group G X)
      ( is-abstractly-transitive-transitive-action-∞-Group)

  is-surjective-mul-right-transitive-action-∞-Group :
    (x : type-transitive-action-∞-Group G X) →
    is-surjective (λ g → mul-transitive-action-∞-Group G X g x)
  is-surjective-mul-right-transitive-action-∞-Group =
    is-surjective-tr-transitive-action-∞-Group (shape-∞-Group G)
```
