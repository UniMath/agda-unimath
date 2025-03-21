# The precategory of commutative rings

```agda
module commutative-algebra.precategory-of-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories
open import category-theory.large-precategories
open import category-theory.precategories

open import commutative-algebra.commutative-rings

open import foundation.universe-levels

open import ring-theory.precategory-of-rings
```

</details>

## Idea

The
{{#concept "precategory of commutative rings" Agda=Commutative-Ring-Large-Precategory}}
consists of [commutative rings](commutative-algebra.commutative-rings.md) and
[homomorphisms of commutative rings](commutative-algebra.homomorphisms-commutative-rings.md).

## Definitions

### The precategory of commutative rings as a full subprecategory of rings

```agda
Commutative-Ring-Full-Large-Subprecategory :
  Full-Large-Subprecategory (λ l → l) Ring-Large-Precategory
Commutative-Ring-Full-Large-Subprecategory = is-commutative-prop-Ring
```

### The large precategory of commutative rings

```agda
Commutative-Ring-Large-Precategory : Large-Precategory lsuc (_⊔_)
Commutative-Ring-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Ring-Large-Precategory)
    ( Commutative-Ring-Full-Large-Subprecategory)
```

### The precategory of commutative rings of universe level `l`

```agda
Commutative-Ring-Precategory : (l : Level) → Precategory (lsuc l) l
Commutative-Ring-Precategory =
  precategory-Large-Precategory Commutative-Ring-Large-Precategory
```
