# Commuting squares of pointed homotopies

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types.commuting-squares-of-pointed-homotopies
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.pointed-2-homotopies funext univalence truncations
open import structured-types.pointed-dependent-functions funext
open import structured-types.pointed-families-of-types
open import structured-types.pointed-homotopies funext univalence truncations
open import structured-types.pointed-types
```

</details>

## Idea

A square of [pointed homotopies](structured-types.pointed-homotopies.md)

```text
          top
      f ------> g
      |         |
 left |         | right
      ∨         ∨
      h ------> i
        bottom
```

is said to be a
{{#concept "commuting square" Disambiguation="pointed homotopies" Agda=coherence-square-pointed-homotopies}}
of pointed homotopies if there is a pointed homotopy
`left ∙h bottom ~∗ top ∙h right `. Such a pointed homotopy is called a
{{#concept "coherence" Disambiguation="commuting square of homotopies" Agda=coherence-square-pointed-homotopies}}
of the square.

## Definitions

### Commuting squares of pointed homotopies

```agda
module _
  {l1 l2 : Level}
  {A : Pointed-Type l1} {B : Pointed-Fam l2 A} {f g h i : pointed-Π A B}
  (top : f ~∗ g) (left : f ~∗ h) (right : g ~∗ i) (bottom : h ~∗ i)
  where

  coherence-square-pointed-homotopies : UU (l1 ⊔ l2)
  coherence-square-pointed-homotopies =
    pointed-2-htpy
      ( concat-pointed-htpy left bottom)
      ( concat-pointed-htpy top right)

  coherence-square-pointed-homotopies' : UU (l1 ⊔ l2)
  coherence-square-pointed-homotopies' =
    pointed-2-htpy
      ( concat-pointed-htpy top right)
      ( concat-pointed-htpy left bottom)
```
