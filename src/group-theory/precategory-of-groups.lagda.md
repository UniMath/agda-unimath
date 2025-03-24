# The precategory of groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.precategory-of-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories funext univalence truncations
open import category-theory.large-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import foundation.universe-levels

open import group-theory.groups funext univalence truncations
open import group-theory.precategory-of-semigroups funext univalence truncations
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
