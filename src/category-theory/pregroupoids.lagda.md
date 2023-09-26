# Pregroupoids

```agda
module category-theory.pregroupoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A pregroupoid is a precategory in which every morphism is an isomorphism.

## Definition

```agda
is-groupoid-Precategory-Prop :
  {l1 l2 : Level} (C : Precategory l1 l2) → Prop (l1 ⊔ l2)
is-groupoid-Precategory-Prop C =
  Π-Prop
    ( obj-Precategory C)
    ( λ x →
      Π-Prop
        ( obj-Precategory C)
        ( λ y →
          Π-Prop
            ( hom-Precategory C x y)
            ( is-iso-prop-Precategory C)))

is-groupoid-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → UU (l1 ⊔ l2)
is-groupoid-Precategory C = type-Prop (is-groupoid-Precategory-Prop C)

Pregroupoid :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Pregroupoid l1 l2 = Σ (Precategory l1 l2) is-groupoid-Precategory
```
