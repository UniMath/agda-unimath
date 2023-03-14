# Pregroupoids

```agda
module category-theory.pregroupoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-precategories
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
is-groupoid-precat-Prop :
  {l1 l2 : Level} (C : Precat l1 l2) → Prop (l1 ⊔ l2)
is-groupoid-precat-Prop C =
  Π-Prop
    ( obj-Precat C)
    ( λ x →
      Π-Prop
        ( obj-Precat C)
        ( λ y →
          Π-Prop
            ( type-hom-Precat C x y)
            ( λ f → is-iso-precat-Prop C f)))

is-groupoid-Precat : {l1 l2 : Level} (C : Precat l1 l2) → UU (l1 ⊔ l2)
is-groupoid-Precat C = type-Prop (is-groupoid-precat-Prop C)

Pregroupoid :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Pregroupoid l1 l2 = Σ (Precat l1 l2) is-groupoid-Precat
```
