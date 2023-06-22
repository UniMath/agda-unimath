# The category of sets

```agda
module foundation.category-of-sets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-precategories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.1-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.isomorphisms-of-sets
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

The **category of sets** consists of sets and functions. There is a category of
sets for each universe level, and there is a large category of sets.

## Definitions

### The precategory of small sets

```agda
Set-Precategory : (l : Level) → Precategory (lsuc l) l
pr1 (Set-Precategory l) = Set l
pr1 (pr2 (Set-Precategory l)) = hom-Set
pr1 (pr1 (pr2 (pr2 (Set-Precategory l)))) g f = g ∘ f
pr2 (pr1 (pr2 (pr2 (Set-Precategory l)))) h g f = refl
pr1 (pr2 (pr2 (pr2 (Set-Precategory l)))) x = id
pr1 (pr2 (pr2 (pr2 (pr2 (Set-Precategory l))))) f = refl
pr2 (pr2 (pr2 (pr2 (pr2 (Set-Precategory l))))) f = refl
```

### The category of small sets

The precategory of sets and functions in a given universe is a category.

```agda
id-iso-Set : {l : Level} {x : Set l} → iso-Set x x
id-iso-Set {l} {x} = id-iso-Precategory (Set-Precategory l) {x}

iso-eq-Set : {l : Level} (x y : Set l) → x ＝ y → iso-Set x y
iso-eq-Set {l} = iso-eq-Precategory (Set-Precategory l)

is-category-Set-Precategory :
  (l : Level) → is-category-Precategory (Set-Precategory l)
is-category-Set-Precategory l x =
  fundamental-theorem-id
    ( is-contr-equiv'
      ( Σ (Set l) (type-equiv-Set x))
      ( equiv-tot (equiv-iso-equiv-Set x))
      ( is-contr-total-equiv-Set x))
    ( iso-eq-Set x)

Set-Category : (l : Level) → Category (lsuc l) l
pr1 (Set-Category l) = Set-Precategory l
pr2 (Set-Category l) = is-category-Set-Precategory l
```

### The large precategory of sets

```agda
Set-Large-Precategory : Large-Precategory lsuc (_⊔_)
obj-Large-Precategory Set-Large-Precategory = Set
hom-Large-Precategory Set-Large-Precategory = hom-Set
comp-hom-Large-Precategory Set-Large-Precategory g f = g ∘ f
id-hom-Large-Precategory Set-Large-Precategory = id
associative-comp-hom-Large-Precategory Set-Large-Precategory h g f = refl
left-unit-law-comp-hom-Large-Precategory Set-Large-Precategory f = refl
right-unit-law-comp-hom-Large-Precategory Set-Large-Precategory f = refl
```

Note that to prove that the large precategory of sets is a large _category_, we
would need the univalence axiom for large types.
