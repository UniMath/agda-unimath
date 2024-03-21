# Eilenberg-Mac Lane spaces

```agda
module higher-group-theory.eilenberg-mac-lane-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.cartesian-product-types
open import foundation.connected-types
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups

open import structured-types.equivalences-h-spaces
open import structured-types.pointed-equivalences
open import structured-types.pointed-types

open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

There are many ways to say what an _Eilenberg-Mac Lane space_ is. The basic idea
is that a pointed connected type `X` is an Eilenberg-Mac Lane space if only one
of its homotopy groups `π n X` is nontrivial. However, recall that the condition
of being `n`-truncated is slightly stronger than the condition that the homotopy
groups `π i X` are trivial for all `i > n`. Indeed, unlike in the setting of
topological spaces or simplicial sets, univalent type theory allows for the
possibility of ∞-connected types, i.e., types of which all homotopy groups are
trivial. In order to avoid examples of Eilenberg-Mac Lane spaces involving such
∞-connected types, we will slightly strengthen the definition of Eilenberg-Mac
Lane spaces. We say that a pointed type `X`is an
{{#concept "Eilengberg-Mac Lane space"}} if`X`is`n-1`-connected and
`n`-truncated. Under this definition there is an equivalence between the
category of groups, resp. abelian groups, and the category of Eilenberg-Mac Lane
spaces of dimension `1`, resp. `n ≥ 2`.

Consider a [group](group-theory.groups.md) `G` and a natural number `n ≥ 1`. A
pointed type `X` is said to be an Eilenberg-Mac Lane space of type `K G n` if
`X` is `(n-1)`-connected and `n`-truncated, and moreover the `n`-th homotopy
group `π n X` is isomorphic to `G`.

There is also a recursive definition of what it means for a
[pointed type](higher-group-theory.higher-groups.md) `X` to be an $n$-th
{{#concept "Eilenberg-Mac Lane space" Agda=is-eilenberg-mac-lane-space}}:

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

### Unspecified Eilenberg-Mac Lane spaces

```agda
module _
  {l1 : Level} (k : 𝕋) (X : Pointed-Type l1)
  where

  is-unspecified-eilenberg-mac-lane-space-𝕋 : UU l1
  is-unspecified-eilenberg-mac-lane-space-𝕋 =
    is-connected k (type-Pointed-Type X) ×
    is-trunc (succ-𝕋 k) (type-Pointed-Type X)

module _
  {l1 : Level} (n : ℕ) (X : Pointed-Type l1)
  where

  is-unspecified-eilenberg-mac-lane-space : UU l1
  is-unspecified-eilenberg-mac-lane-space =
    is-unspecified-eilenberg-mac-lane-space-𝕋
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
    equiv-H-Space (h-space-Group G) (iterated-loop-space-H-Space n X)
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
