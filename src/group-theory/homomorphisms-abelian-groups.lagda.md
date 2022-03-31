# Homomorphisms of abelian groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.homomorphisms-abelian-groups where

open import category-theory.large-precategories using (Large-Precat)

open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (is-equiv)
open import foundation.functions using (id)
open import foundation.identity-types using (Id)
open import foundation.sets using (is-set; UU-Set)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import group-theory.abelian-groups using
  ( Ab; type-Ab; semigroup-Ab; group-Ab; add-Ab; zero-Ab; neg-Ab)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group; map-hom-Group; preserves-mul-hom-Group; htpy-hom-Group;
    refl-htpy-hom-Group; htpy-eq-hom-Group; is-contr-total-htpy-hom-Group;
    is-equiv-htpy-eq-hom-Group; eq-htpy-hom-Group; is-set-type-hom-Group;
    id-hom-Group; comp-hom-Group; hom-Group; preserves-unit-hom-Group;
    preserves-inverses-hom-Group)
open import group-theory.homomorphisms-semigroups using
  ( preserves-mul-Semigroup; preserves-mul-id-Semigroup;
    associative-comp-hom-Semigroup; left-unit-law-comp-hom-Semigroup;
    right-unit-law-comp-hom-Semigroup)

open import ring-theory.rings
```

## Idea

Homomorphisms between abelian groups are just homomorphisms between their underlying groups.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where
  
  preserves-add : (type-Ab A → type-Ab B) → UU (l1 ⊔ l2)
  preserves-add = preserves-mul-Semigroup (semigroup-Ab A) (semigroup-Ab B)

  hom-Ab : UU-Set (l1 ⊔ l2)
  hom-Ab = hom-Group (group-Ab A) (group-Ab B)

  type-hom-Ab : UU (l1 ⊔ l2)
  type-hom-Ab = type-hom-Group (group-Ab A) (group-Ab B)

  map-hom-Ab : type-hom-Ab → type-Ab A → type-Ab B
  map-hom-Ab = map-hom-Group (group-Ab A) (group-Ab B)

  preserves-add-hom-Ab : (f : type-hom-Ab) → preserves-add (map-hom-Ab f)
  preserves-add-hom-Ab f = preserves-mul-hom-Group (group-Ab A) (group-Ab B) f

  preserves-zero-Ab :
    (f : type-hom-Ab) → Id (map-hom-Ab f (zero-Ab A)) (zero-Ab B)
  preserves-zero-Ab f = preserves-unit-hom-Group (group-Ab A) (group-Ab B) f

  preserves-neg-Ab :
    (f : type-hom-Ab) (x : type-Ab A) →
    Id (map-hom-Ab f (neg-Ab A x)) (neg-Ab B (map-hom-Ab f x))
  preserves-neg-Ab f =
    preserves-inverses-hom-Group (group-Ab A) (group-Ab B) f
```

### Characterization of the identity type of the abelian group homomorphisms

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where
  
  htpy-hom-Ab : (f g : type-hom-Ab A B) → UU (l1 ⊔ l2)
  htpy-hom-Ab f g = htpy-hom-Group (group-Ab A) (group-Ab B) f g

  refl-htpy-hom-Ab : (f : type-hom-Ab A B) → htpy-hom-Ab f f
  refl-htpy-hom-Ab f = refl-htpy-hom-Group (group-Ab A) (group-Ab B) f

  htpy-eq-hom-Ab : (f g : type-hom-Ab A B) → Id f g → htpy-hom-Ab f g
  htpy-eq-hom-Ab f g = htpy-eq-hom-Group (group-Ab A) (group-Ab B) f g

  abstract
    is-contr-total-htpy-hom-Ab :
      (f : type-hom-Ab A B) → is-contr (Σ (type-hom-Ab A B) (htpy-hom-Ab f))
    is-contr-total-htpy-hom-Ab f =
      is-contr-total-htpy-hom-Group (group-Ab A) (group-Ab B) f

  abstract
    is-equiv-htpy-eq-hom-Ab :
      (f g : type-hom-Ab A B) → is-equiv (htpy-eq-hom-Ab f g)
    is-equiv-htpy-eq-hom-Ab f g =
      is-equiv-htpy-eq-hom-Group (group-Ab A) (group-Ab B) f g

  eq-htpy-hom-Ab : {f g : type-hom-Ab A B} → htpy-hom-Ab f g → Id f g
  eq-htpy-hom-Ab = eq-htpy-hom-Group (group-Ab A) (group-Ab B)

  is-set-hom-Ab : is-set (type-hom-Ab A B)
  is-set-hom-Ab = is-set-type-hom-Group (group-Ab A) (group-Ab B)
```

### The identity morphism of abelian groups

```agda
preserves-add-id : {l : Level} (A : Ab l) → preserves-add A A id
preserves-add-id A = preserves-mul-id-Semigroup (semigroup-Ab A)

id-hom-Ab : {l1 : Level} (A : Ab l1) → type-hom-Ab A A
id-hom-Ab A = id-hom-Group (group-Ab A)
```

### Composition of morphisms of abelian groups

```agda
comp-hom-Ab :
  { l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3) →
  ( type-hom-Ab B C) → (type-hom-Ab A B) → (type-hom-Ab A C)
comp-hom-Ab A B C =
  comp-hom-Group (group-Ab A) (group-Ab B) (group-Ab C)
```

### Associativity of composition of morphisms of abelian groups

```agda
associative-comp-hom-Ab :
  { l1 l2 l3 l4 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3) (D : Ab l4) →
  ( h : type-hom-Ab C D) (g : type-hom-Ab B C) (f : type-hom-Ab A B) →
  Id (comp-hom-Ab A B D (comp-hom-Ab B C D h g) f)
     (comp-hom-Ab A C D h (comp-hom-Ab A B C g f))
associative-comp-hom-Ab A B C D =
  associative-comp-hom-Semigroup
    ( semigroup-Ab A)
    ( semigroup-Ab B)
    ( semigroup-Ab C)
    ( semigroup-Ab D)
```

### The unit laws for composition of abelian groups

```agda
left-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : type-hom-Ab A B) → Id (comp-hom-Ab A B B (id-hom-Ab B) f) f
left-unit-law-comp-hom-Ab A B =
  left-unit-law-comp-hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)

right-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : type-hom-Ab A B) → Id (comp-hom-Ab A A B f (id-hom-Ab A)) f
right-unit-law-comp-hom-Ab A B =
  right-unit-law-comp-hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)
```

### The large precategory of abelian groups

```agda
ab-Precat : Large-Precat lsuc (λ l1 l2 → l1 ⊔ l2)
Large-Precat.obj-Large-Precat ab-Precat = Ab
Large-Precat.hom-Large-Precat ab-Precat = hom-Ab
Large-Precat.comp-hom-Large-Precat ab-Precat {X = A} {B} {C} = comp-hom-Ab A B C
Large-Precat.id-hom-Large-Precat ab-Precat {X = A} = id-hom-Ab A
Large-Precat.associative-comp-hom-Large-Precat ab-Precat {X = A} {B} {C} {D} =
  associative-comp-hom-Ab A B C D
Large-Precat.left-unit-law-comp-hom-Large-Precat ab-Precat {X = A} {B} =
  left-unit-law-comp-hom-Ab A B
Large-Precat.right-unit-law-comp-hom-Large-Precat ab-Precat {X = A} {B} =
  right-unit-law-comp-hom-Ab A B
```
