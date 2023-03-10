# Categories

```agda
module category-theory.categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-precategories
open import category-theory.precategories

open import foundation.1-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.isomorphisms-of-sets
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A category in Homotopy Type Theory is a precategory for which the identities between the objects are the isomorphisms. More specifically, an equality between objects gives rise to an isomorphism between them, by the J-rule. A precategory is a category if this function is an equivalence. Note: being a category is a proposition since `is-equiv` is a proposition.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  is-category-Precat-Prop : Prop (l1 ⊔ l2)
  is-category-Precat-Prop =
    Π-Prop
      ( obj-Precat C)
      ( λ x →
        Π-Prop (obj-Precat C) (λ y → is-equiv-Prop (iso-eq-Precat C x y)))

  is-category-Precat : UU (l1 ⊔ l2)
  is-category-Precat = type-Prop is-category-Precat-Prop

Cat : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cat l1 l2 = Σ (Precat l1 l2) is-category-Precat

module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  precat-Cat : Precat l1 l2
  precat-Cat = pr1 C

  obj-Cat : UU l1
  obj-Cat = obj-Precat precat-Cat

  hom-Cat : obj-Cat → obj-Cat → Set l2
  hom-Cat = hom-Precat precat-Cat

  type-hom-Cat : obj-Cat → obj-Cat → UU l2
  type-hom-Cat = type-hom-Precat precat-Cat

  is-set-type-hom-Cat : (x y : obj-Cat) → is-set (type-hom-Cat x y)
  is-set-type-hom-Cat = is-set-type-hom-Precat precat-Cat

  comp-hom-Cat :
    {x y z : obj-Cat} → type-hom-Cat y z → type-hom-Cat x y → type-hom-Cat x z
  comp-hom-Cat = comp-hom-Precat precat-Cat

  assoc-comp-hom-Cat :
    {x y z w : obj-Cat}
    (h : type-hom-Cat z w) (g : type-hom-Cat y z) (f : type-hom-Cat x y) →
    comp-hom-Cat (comp-hom-Cat h g) f ＝ comp-hom-Cat h (comp-hom-Cat g f)
  assoc-comp-hom-Cat = assoc-comp-hom-Precat precat-Cat

  id-hom-Cat : {x : obj-Cat} → type-hom-Cat x x
  id-hom-Cat = id-hom-Precat precat-Cat

  left-unit-law-comp-hom-Cat :
    {x y : obj-Cat} (f : type-hom-Cat x y) → comp-hom-Cat id-hom-Cat f ＝ f
  left-unit-law-comp-hom-Cat = left-unit-law-comp-hom-Precat precat-Cat

  right-unit-law-comp-hom-Cat :
    {x y : obj-Cat} (f : type-hom-Cat x y) → comp-hom-Cat f id-hom-Cat ＝ f
  right-unit-law-comp-hom-Cat = right-unit-law-comp-hom-Precat precat-Cat

  is-category-Cat : is-category-Precat precat-Cat
  is-category-Cat = pr2 C
```

## Examples

### The category of sets and functions

The precategory of sets and functions in a given universe is a category.

```agda
id-iso-Set : {l : Level} {x : Set l} → iso-Set x x
id-iso-Set {l} {x} = id-iso-Precat (Set-Precat l) {x}

iso-eq-Set : {l : Level} (x y : Set l) → x ＝ y → iso-Set x y
iso-eq-Set {l} = iso-eq-Precat (Set-Precat l)

is-category-Set-Precat : (l : Level) → is-category-Precat (Set-Precat l)
is-category-Set-Precat l x =
  fundamental-theorem-id
    ( is-contr-equiv'
      ( Σ (Set l) (type-equiv-Set x))
      ( equiv-tot (equiv-iso-equiv-Set x))
      ( is-contr-total-equiv-Set x))
    ( iso-eq-Set x)

Set-Cat : (l : Level) → Cat (lsuc l) l
pr1 (Set-Cat l) = Set-Precat l
pr2 (Set-Cat l) = is-category-Set-Precat l
```

## Properties

### The objects in a category form a 1-type

The type of identities between two objects in a category is equivalent to the type of isomorphisms between them. But this type is a set, and thus the identity type is a set.

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  is-1-type-obj-Cat : is-1-type (obj-Cat C)
  is-1-type-obj-Cat x y =
    is-set-is-equiv
      ( iso-Precat (precat-Cat C) x y)
      ( iso-eq-Precat (precat-Cat C) x y)
      ( is-category-Cat C x y)
      ( is-set-iso-Precat (precat-Cat C) x y)

  obj-Cat-1-Type : 1-Type l1
  pr1 obj-Cat-1-Type = obj-Cat C
  pr2 obj-Cat-1-Type = is-1-type-obj-Cat
```
