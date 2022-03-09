# Categories

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.categories where

open import categories.isomorphisms-precategories using
  ( iso-Precat; id-iso-Precat; iso-eq-Precat; is-set-iso-Precat)
open import categories.precategories using
  ( Precat; obj-Precat; id-Precat; hom-Precat; type-hom-Precat;
    is-set-type-hom-Precat; comp-Precat; assoc-comp-Precat;
    left-unit-law-comp-Precat; right-unit-law-comp-Precat)
open import foundation.1-types using (is-1-type; UU-1-Type)
open import foundation.contractible-types using (is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pr1; pr2)
open import foundation.equivalences using (is-equiv-Prop)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (Id; refl)
open import foundation.isomorphisms-of-sets using
  ( iso-Set; equiv-iso-equiv-Set)
open import foundation.propositions using (UU-Prop; Π-Prop; type-Prop)
open import foundation.sets using
  ( UU-Set; is-set; is-set-is-equiv; hom-Set; type-equiv-Set;
    is-contr-total-equiv-Set)
open import foundation.universe-levels using (UU; Level; _⊔_; lsuc)
```

## Idea

A category in Homotopy Type Theory is a precategory for which the identities between the objects are the isomorphisms. More specifically, an equality between objects gives rise to an isomorphism between them, by the J-rule. A precategory is a category if this function is an equivalence. Note: being a category is a proposition since `is-equiv` is a proposition.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  is-category-Precat-Prop : UU-Prop (l1 ⊔ l2)
  is-category-Precat-Prop =
    Π-Prop (obj-Precat C)
      ( λ x → Π-Prop (obj-Precat C) (λ y → is-equiv-Prop (iso-eq-Precat C x y)))

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

  hom-Cat : obj-Cat → obj-Cat → UU-Set l2
  hom-Cat = hom-Precat precat-Cat

  type-hom-Cat : obj-Cat → obj-Cat → UU l2
  type-hom-Cat = type-hom-Precat precat-Cat

  is-set-type-hom-Cat : (x y : obj-Cat) → is-set (type-hom-Cat x y)
  is-set-type-hom-Cat = is-set-type-hom-Precat precat-Cat

  comp-Cat : {x y z : obj-Cat} → type-hom-Cat y z → type-hom-Cat x y → type-hom-Cat x z
  comp-Cat = comp-Precat precat-Cat

  assoc-comp-Cat :
    {x y z w : obj-Cat}
    (h : type-hom-Cat z w) (g : type-hom-Cat y z) (f : type-hom-Cat x y) →
    Id ( comp-Cat (comp-Cat h g) f)
       ( comp-Cat h (comp-Cat g f))
  assoc-comp-Cat = assoc-comp-Precat precat-Cat

  id-Cat : {x : obj-Cat} → type-hom-Cat x x
  id-Cat = id-Precat precat-Cat

  left-unit-law-comp-Cat :
    {x y : obj-Cat} (f : type-hom-Cat x y) → Id (comp-Cat id-Cat f) f
  left-unit-law-comp-Cat = left-unit-law-comp-Precat precat-Cat

  right-unit-law-comp-Cat :
    {x y : obj-Cat} (f : type-hom-Cat x y) → Id (comp-Cat f id-Cat) f
  right-unit-law-comp-Cat = right-unit-law-comp-Precat precat-Cat

  is-category-Cat : is-category-Precat precat-Cat
  is-category-Cat = pr2 C
```

## Examples

### The category of sets and functions

The precategory of sets and functions in a given universe is a category.

```agda
Set-Precat : (l : Level) → Precat (lsuc l) l
pr1 (Set-Precat l) = UU-Set l
pr1 (pr2 (Set-Precat l)) = hom-Set
pr1 (pr1 (pr2 (pr2 (Set-Precat l)))) g f = g ∘ f
pr2 (pr1 (pr2 (pr2 (Set-Precat l)))) h g f = refl
pr1 (pr2 (pr2 (pr2 (Set-Precat l)))) x = id
pr1 (pr2 (pr2 (pr2 (pr2 (Set-Precat l))))) f = refl
pr2 (pr2 (pr2 (pr2 (pr2 (Set-Precat l))))) f = refl

id-iso-Set : {l : Level} {x : UU-Set l} → iso-Set x x
id-iso-Set {l} {x} = id-iso-Precat (Set-Precat l) {x}

iso-eq-Set : {l : Level} (x y : UU-Set l) → Id x y → iso-Set x y
iso-eq-Set {l} = iso-eq-Precat (Set-Precat l)

is-category-Set-Precat : (l : Level) → is-category-Precat (Set-Precat l)
is-category-Set-Precat l x =
  fundamental-theorem-id x
    ( id-iso-Set {l} {x})
    ( is-contr-equiv'
      ( Σ (UU-Set l) (type-equiv-Set x))
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

  obj-Cat-1-Type : UU-1-Type l1
  pr1 obj-Cat-1-Type = obj-Cat C
  pr2 obj-Cat-1-Type = is-1-type-obj-Cat
```
