# Large categories

```agda
module category-theory.large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-large-precategories
open import category-theory.large-precategories

open import foundation.equivalences
open import foundation.large-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A large category in Homotopy Type Theory is a large precategory for which the
identities between the objects are the isomorphisms. More specifically, an
equality between objects gives rise to an isomorphism between them, by the
J-rule. A large precategory is a large category if this function is an
equivalence. Note: being a large category is a proposition since `is-equiv` is a
proposition.

## Definition

```agda
is-category-Large-Precat :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Precat α β) → UUω
is-category-Large-Precat C =
  {l : Level} (X Y : obj-Large-Precat C l) →
  is-equiv (iso-eq-Large-Precat C X Y)

Large-Cat : (α : Level → Level) (β : Level → Level → Level) → UUω
Large-Cat α β = Σω (Large-Precat α β) is-category-Large-Precat

precat-Large-Cat :
  {α : Level → Level} {β : Level → Level → Level} →
  Large-Cat α β → Large-Precat α β
precat-Large-Cat = prω1

is-category-Large-Cat :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Cat α β) → is-category-Large-Precat (precat-Large-Cat C)
is-category-Large-Cat = prω2
```
