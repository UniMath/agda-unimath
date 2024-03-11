# The precategory of commutative monoids

```agda
module group-theory.precategory-of-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.precategory-of-monoids
```

</details>

## Idea

The **precategory of commutative monoids** consists of commutative monoids and
homomorphisms of monoids.

## Definitions

### The precategory of commutative monoids as a full subprecategory of monoids

```agda
Commutative-Monoid-Full-Large-Subprecategory :
  Full-Large-Subprecategory (λ l → l) Monoid-Large-Precategory
Commutative-Monoid-Full-Large-Subprecategory = is-commutative-prop-Monoid
```

### The large precategory of commutative monoids

```agda
Commutative-Monoid-Large-Precategory : Large-Precategory lsuc (_⊔_)
Commutative-Monoid-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Monoid-Large-Precategory)
    ( Commutative-Monoid-Full-Large-Subprecategory)
```

### The precategory of small commutative monoids

```agda
Commutative-Monoid-Precategory : (l : Level) → Precategory (lsuc l) l
Commutative-Monoid-Precategory =
  precategory-Large-Precategory Commutative-Monoid-Large-Precategory
```
