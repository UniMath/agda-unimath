# Isomorphisms of concrete groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.isomorphisms-concrete-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories funext

open import foundation.universe-levels

open import group-theory.concrete-groups funext
open import group-theory.precategory-of-concrete-groups funext
```

</details>

## Idea

**Isomorphisms** of [concrete groups](group-theory.concrete-groups.md) are
[isomorphisms](category-theory.isomorphisms-in-large-precategories.md) in the
[large precategory of concrete groups](group-theory.precategory-of-concrete-groups.md).

## Definition

```agda
iso-Concrete-Group :
  {l1 l2 : Level} → Concrete-Group l1 → Concrete-Group l2 → UU (l1 ⊔ l2)
iso-Concrete-Group = iso-Large-Precategory Concrete-Group-Large-Precategory
```

## Properties

### Equivalences of concrete groups are isomorphisms of concrete groups

This remains to be shown.
[#736](https://github.com/UniMath/agda-unimath/issues/736)
