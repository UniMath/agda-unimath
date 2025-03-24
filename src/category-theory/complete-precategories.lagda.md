# Complete precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.complete-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cones-precategories funext univalence truncations
open import category-theory.functors-precategories funext univalence truncations
open import category-theory.limits-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations
open import category-theory.terminal-objects-precategories funext univalence truncations

open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "complete precategory" Agda=is-complete-Precategory}} is a
[precategory](category-theory.precategories.md) that has all
[limits](category-theory.limits-precategories.md) for diagrams from a specified
universe.

More precisely, we say that a precategory `D` is `(l1 , l2)`-complete if for any
`C : Precategory l1 l2` and any
[functor](category-theory.functors-precategories.md) `F : C → D` the type of
limits of `F` is inhabited.

## Definition

```agda
is-complete-Precategory :
  (l1 l2 : Level) {l3 l4 : Level}
  (D : Precategory l3 l4) →
  UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4)
is-complete-Precategory l1 l2 D =
  (C : Precategory l1 l2) (F : functor-Precategory C D) →
  limit-Precategory C D F
```
