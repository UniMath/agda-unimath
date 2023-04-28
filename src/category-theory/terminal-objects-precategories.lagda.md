# Terminal object of a precategory

```agda
module category-theory.terminal-objects-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

The terminal object of a precategory (if it exists) is an object with the
universal property that there is a unique morphism into it from any object.

## Definition

```agda
terminal-object-Precat : {l1 l2 : Level} (C : Precat l1 l2) → UU (l1 ⊔ l2)
terminal-object-Precat C =
  Σ (obj-Precat C) λ t →
    (x : obj-Precat C) → is-contr (type-hom-Precat C x t)

module _
  {l1 l2 : Level} (C : Precat l1 l2)
  (t : terminal-object-Precat C)
  where

  object-terminal-object-Precat : obj-Precat C
  object-terminal-object-Precat = pr1 t

  morphism-terminal-object-Precat :
    (x : obj-Precat C) →
    type-hom-Precat C x object-terminal-object-Precat
  morphism-terminal-object-Precat x = pr1 (pr2 t x)

  is-unique-morphism-terminal-object-Precat :
    (x : obj-Precat C) →
    (f : type-hom-Precat C x object-terminal-object-Precat) →
    morphism-terminal-object-Precat x ＝ f
  is-unique-morphism-terminal-object-Precat x = pr2 (pr2 t x)
```
