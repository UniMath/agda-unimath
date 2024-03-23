# The precategory of groups

```agda
module group-theory.precategory-of-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import group-theory.groups
open import group-theory.precategory-of-semigroups
```

</details>

## Definition

### The precategory of groups as a full subprecategory of the precategory of semigroups

```agda
Group-Full-Large-Subprecategory :
  Full-Large-Subprecategory (λ l → l) Semigroup-Large-Precategory
Group-Full-Large-Subprecategory = is-group-prop-Semigroup
```

### The large precategory of groups

```agda
Group-Large-Precategory : Large-Precategory lsuc (_⊔_)
Group-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Semigroup-Large-Precategory)
    ( Group-Full-Large-Subprecategory)
```

### The small precategories of groups

```agda
Group-Precategory : (l : Level) → Precategory (lsuc l) l
Group-Precategory = precategory-Large-Precategory Group-Large-Precategory
```
