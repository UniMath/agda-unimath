# Commuting squares of morphisms in precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.commuting-squares-of-morphisms-in-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-set-magmoids funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import foundation.universe-levels
```

</details>

## Idea

A square of morphisms

```text
  x ------> y
  |         |
  |         |
  ∨         ∨
  z ------> w
```

in a [precategory](category-theory.precategories.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between both
composites:

```text
  bottom ∘ left ＝ right ∘ top.
```

## Definitions

```agda
coherence-square-hom-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) {x y z w : obj-Precategory C}
  (top : hom-Precategory C x y)
  (left : hom-Precategory C x z)
  (right : hom-Precategory C y w)
  (bottom : hom-Precategory C z w) →
  UU l2
coherence-square-hom-Precategory C =
  coherence-square-hom-Set-Magmoid (set-magmoid-Precategory C)
```
