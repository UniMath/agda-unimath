# The precategory of finite posets

```agda
module order-theory.precategory-of-finite-posets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import order-theory.finite-posets
open import order-theory.precategory-of-posets
```

</details>

## Idea

The **(large) precategory of finite posets** consists of
[finite posets](order-theory.finite-posets.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md) and is
exhibited as a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
[precategory of posets](order-theory.precategory-of-posets.md).

## Definitions

### The large precategory of finite posets

```agda
parametric-Finite-Poset-Full-Large-Subprecategory :
  (α β : Level → Level) →
  Full-Large-Subprecategory
    ( λ l → α l ⊔ β l)
    ( parametric-Poset-Large-Precategory α β)
parametric-Finite-Poset-Full-Large-Subprecategory α β = is-finite-Poset-Prop

Finite-Poset-Large-Precategory :
  Large-Precategory lsuc (_⊔_)
Finite-Poset-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Poset-Large-Precategory)
    ( parametric-Finite-Poset-Full-Large-Subprecategory (λ l → l) (λ l → l))
```

### The precategory of finite posets of universe level `l`

```agda
Finite-Poset-Precategory : (l : Level) → Precategory (lsuc l) l
Finite-Poset-Precategory =
  precategory-Large-Precategory Finite-Poset-Large-Precategory
```
