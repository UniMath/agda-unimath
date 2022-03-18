# Homomorphisms of abelian groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.homomorphisms-abelian-groups where

open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (is-equiv)
open import foundation.functions using (id)
open import foundation.identity-types using (Id)
open import foundation.sets using (is-set)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.abelian-groups using
  ( Ab; type-Ab; semigroup-Ab; group-Ab)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group; map-hom-Group; preserves-mul-hom-Group; htpy-hom-Group;
    refl-htpy-hom-Group; htpy-eq-hom-Group; is-contr-total-htpy-hom-Group;
    is-equiv-htpy-eq-hom-Group; eq-htpy-hom-Group; is-set-type-hom-Group;
    id-hom-Group; comp-hom-Group)
open import group-theory.homomorphisms-semigroups using
  ( preserves-mul-Semigroup; preserves-mul-id-Semigroup;
    associative-comp-hom-Semigroup; left-unit-law-comp-hom-Semigroup;
    right-unit-law-comp-hom-Semigroup)
```

## Idea

Homomorphisms between abelian groups are just homomorphisms between their underlying groups.

## Definition

```agda
preserves-add :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  (type-Ab A → type-Ab B) → UU (l1 ⊔ l2)
preserves-add A B = preserves-mul-Semigroup (semigroup-Ab A) (semigroup-Ab B)

hom-Ab :
  {l1 l2 : Level} → Ab l1 → Ab l2 → UU (l1 ⊔ l2)
hom-Ab A B = type-hom-Group (group-Ab A) (group-Ab B)

map-hom-Ab :
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  hom-Ab A B → type-Ab A → type-Ab B
map-hom-Ab A B = map-hom-Group (group-Ab A) (group-Ab B)

preserves-add-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  ( f : hom-Ab A B) → preserves-add A B (map-hom-Ab A B f)
preserves-add-Ab A B f = preserves-mul-hom-Group (group-Ab A) (group-Ab B) f

{- We characterize the identity type of the abelian group homomorphisms. -}

htpy-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f g : hom-Ab A B) → UU (l1 ⊔ l2)
htpy-hom-Ab A B f g = htpy-hom-Group (group-Ab A) (group-Ab B) f g

refl-htpy-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  ( f : hom-Ab A B) → htpy-hom-Ab A B f f
refl-htpy-hom-Ab A B f =
  refl-htpy-hom-Group (group-Ab A) (group-Ab B) f

htpy-eq-hom-Ab :
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  (f g : hom-Ab A B) → Id f g → htpy-hom-Ab A B f g
htpy-eq-hom-Ab A B f g = htpy-eq-hom-Group (group-Ab A) (group-Ab B) f g

abstract
  is-contr-total-htpy-hom-Ab :
    { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
    ( f : hom-Ab A B) →
    is-contr (Σ (hom-Ab A B) (htpy-hom-Ab A B f))
  is-contr-total-htpy-hom-Ab A B f =
    is-contr-total-htpy-hom-Group (group-Ab A) (group-Ab B) f

abstract
  is-equiv-htpy-eq-hom-Ab :
    { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
    ( f g : hom-Ab A B) → is-equiv (htpy-eq-hom-Ab A B f g)
  is-equiv-htpy-eq-hom-Ab A B f g =
    is-equiv-htpy-eq-hom-Group (group-Ab A) (group-Ab B) f g

eq-htpy-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  { f g : hom-Ab A B} → htpy-hom-Ab A B f g → Id f g
eq-htpy-hom-Ab A B =
  eq-htpy-hom-Group (group-Ab A) (group-Ab B)

is-set-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  is-set (hom-Ab A B)
is-set-hom-Ab A B = is-set-type-hom-Group (group-Ab A) (group-Ab B)

preserves-add-id :
  {l : Level} (A : Ab l) → preserves-add A A id
preserves-add-id A = preserves-mul-id-Semigroup (semigroup-Ab A)

id-hom-Ab :
  { l1 : Level} (A : Ab l1) → hom-Ab A A
id-hom-Ab A = id-hom-Group (group-Ab A)

comp-hom-Ab :
  { l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3) →
  ( hom-Ab B C) → (hom-Ab A B) → (hom-Ab A C)
comp-hom-Ab A B C =
  comp-hom-Group (group-Ab A) (group-Ab B) (group-Ab C)

associative-comp-hom-Ab :
  { l1 l2 l3 l4 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3) (D : Ab l4) →
  ( h : hom-Ab C D) (g : hom-Ab B C) (f : hom-Ab A B) →
  Id (comp-hom-Ab A B D (comp-hom-Ab B C D h g) f)
     (comp-hom-Ab A C D h (comp-hom-Ab A B C g f))
associative-comp-hom-Ab A B C D =
  associative-comp-hom-Semigroup
    ( semigroup-Ab A)
    ( semigroup-Ab B)
    ( semigroup-Ab C)
    ( semigroup-Ab D)

left-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : hom-Ab A B) → Id (comp-hom-Ab A B B (id-hom-Ab B) f) f
left-unit-law-comp-hom-Ab A B =
  left-unit-law-comp-hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)

right-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : hom-Ab A B) → Id (comp-hom-Ab A A B f (id-hom-Ab A)) f
right-unit-law-comp-hom-Ab A B =
  right-unit-law-comp-hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)
```
