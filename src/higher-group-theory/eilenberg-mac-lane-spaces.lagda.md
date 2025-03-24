# Eilenberg-Mac Lane spaces

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module higher-group-theory.eilenberg-mac-lane-spaces
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types funext univalence truncations
open import foundation.cartesian-product-types funext univalence
open import foundation.connected-types funext univalence truncations
open import foundation.dependent-products-truncated-types funext
open import foundation.truncated-types funext univalence
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.abelian-groups funext univalence truncations
open import group-theory.groups funext univalence truncations

open import structured-types.equivalences-h-spaces funext univalence truncations
open import structured-types.pointed-equivalences funext univalence truncations
open import structured-types.pointed-types

open import synthetic-homotopy-theory.iterated-loop-spaces funext univalence truncations
open import synthetic-homotopy-theory.loop-spaces funext univalence truncations
```

</details>

## Idea

There are many ways to say what an _Eilenberg-Mac Lane space_ is. The basic idea
is that a [pointed](structured-types.pointed-types.md)
[connected](foundation.0-connected-types.md) type `X` is an Eilenberg-Mac Lane
space if only one of its homotopy groups `π n X` is
[nontrivial](group-theory.nontrivial-groups.md). However, recall that the
condition of being [`n`-truncated](foundation-core.truncated-types.md) is
slightly stronger than the condition that the homotopy groups `π i X` are
[trivial](group-theory.trivial-groups.md) for all `i > n`. Indeed, unlike in the
setting of topological spaces or simplicial sets, univalent type theory allows
for the possibility of ∞-connected types, i.e., types of which all homotopy
groups are trivial. In order to avoid examples of Eilenberg-Mac Lane spaces
possibly involving nontrivial ∞-connected types, we will slightly strengthen the
definition of Eilenberg-Mac Lane spaces. We say that a pointed type `X`is an
{{#concept "Eilenberg-Mac Lane space"}} if`X`is`n-1`-connected and
`n`-truncated. Under this definition there is an
[equivalence](category-theory.equivalences-of-categories.md) between the
[category of groups](group-theory.category-of-groups.md), resp. the
[category of abelian groups](group-theory.category-of-abelian-groups.md), and
the category of Eilenberg-Mac Lane spaces of dimension `1`, resp. `n ≥ 2`.

Consider a [group](group-theory.groups.md) `G` and a
[natural number](elementary-number-theory.natural-numbers.md) `n ≥ 1`. A pointed
type `X` is said to be an Eilenberg-Mac Lane space of type `K G n` if `X` is
[`(n-1)`-connected](foundation.connected-types.md) and
[`n`-truncated](foundation-core.truncated-types.md), and moreover the `n`-th
homotopy group `π n X` is [isomorphic](group-theory.isomorphisms-groups.md) to
`G`.

There is also a recursive definition of what it means for a pointed type `X` to
be an $n$-th
{{#concept "Eilenberg-Mac Lane space" Agda=is-eilenberg-mac-lane-space-Group}}:

- We say that `X` is a **first Eilenberg-Mac Lane space** if `X` is
  `0`-connected and there is a
  [pointed equivalence](structured-types.pointed-equivalences.md)

  ```text
    Ω X ≃ G
  ```

  that maps concatenation in the
  [loop space](synthetic-homotopy-theory.loop-spaces.md) `Ω X` to the group
  operation on `G`.

- We say that `X` is an `(n+1)`-st Eilenberg-Mac Lane space if `X` is
  `0`-connected and `Ω X` is an `n`-th Eilenberg-Mac Lane space.

## Definitions

### Eilenberg-Mac Lane spaces

We introduce the most general notion of an (unspecified) Eilenberg-Mac Lane
space to be a pointed `n`-connected `(n+1)`-truncated type. Eilenberg-Mac Lane
spaces in this definition aren't equipped with a group isomorphism from their
nontrivial homotopy group to a given group `G`, so in this sense they are
"unspecified".

```agda
module _
  {l1 : Level} (k : 𝕋) (X : Pointed-Type l1)
  where

  is-eilenberg-mac-lane-space-𝕋 : UU l1
  is-eilenberg-mac-lane-space-𝕋 =
    is-connected k (type-Pointed-Type X) ×
    is-trunc (succ-𝕋 k) (type-Pointed-Type X)

module _
  {l1 : Level} (n : ℕ) (X : Pointed-Type l1)
  where

  is-eilenberg-mac-lane-space : UU l1
  is-eilenberg-mac-lane-space =
    is-eilenberg-mac-lane-space-𝕋
      ( truncation-level-minus-one-ℕ n)
      ( X)
```

### Eilenberg-Mac Lane spaces specified by groups

```agda
module _
  {l1 l2 : Level} (G : Group l1)
  where

  is-eilenberg-mac-lane-space-Group :
    (n : ℕ) (X : Pointed-Type l2) → UU (l1 ⊔ l2)
  is-eilenberg-mac-lane-space-Group 0 X =
    pointed-type-Group G ≃∗ X
  is-eilenberg-mac-lane-space-Group (succ-ℕ n) X =
    is-connected (truncation-level-ℕ n) (type-Pointed-Type X) ×
    equiv-H-Space (h-space-Group G) (Ω-H-Space (iterated-loop-space n X))
```

### Eilenberg-Mac Lane spaces specified by abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1)
  where

  is-eilenberg-mac-lane-space-Ab :
    (n : ℕ) (X : Pointed-Type l2) → UU (l1 ⊔ l2)
  is-eilenberg-mac-lane-space-Ab =
    is-eilenberg-mac-lane-space-Group (group-Ab A)
```
