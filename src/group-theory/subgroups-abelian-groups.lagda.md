---
title: Subgroups of abelian groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.subgroups-abelian-groups where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.identity-types using (Id)
open import foundation.propositions using (is-prop)
open import foundation.sets using (is-set; Set)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)

open import group-theory.abelian-groups using
  ( Ab; group-Ab; type-Ab; commutative-add-Ab)
open import group-theory.embeddings-groups using
  ( emb-Group; emb-Group-Slice; emb-group-slice-Subgroup)
open import group-theory.groups using (Group)
open import group-theory.homomorphisms-abelian-groups using
  ( preserves-add-Ab; type-hom-Ab; preserves-zero-Ab; preserves-negatives-Ab)
open import group-theory.semigroups using (Semigroup)
open import group-theory.subgroups using
  ( subset-Group; is-set-subset-Group; contains-unit-subset-Group;
    is-prop-contains-unit-subset-Group; is-closed-under-mul-subset-Group;
    is-prop-is-closed-under-mul-subset-Group; is-closed-under-inv-subset-Group;
    is-prop-is-closed-under-inv-subset-Group; is-subgroup-subset-Group;
    is-prop-is-subgroup-subset-Group; Subgroup; subset-Subgroup;
    is-emb-subset-Subgroup; is-in-Subgroup; is-prop-is-in-Subgroup;
    is-subgroup-Subgroup; contains-unit-Subgroup; is-closed-under-mul-Subgroup;
    is-closed-under-inv-Subgroup; type-group-Subgroup;
    map-inclusion-group-Subgroup;
    is-emb-inclusion-group-Subgroup; eq-subgroup-eq-group; set-group-Subgroup;
    unit-Subgroup; mul-Subgroup; inv-Subgroup;
    associative-mul-Subgroup; left-unit-law-mul-Subgroup;
    right-unit-law-mul-Subgroup; left-inverse-law-mul-Subgroup;
    right-inverse-law-mul-Subgroup; group-Subgroup;
    preserves-mul-inclusion-group-Subgroup; inclusion-group-Subgroup;
    semigroup-Subgroup; preserves-unit-inclusion-group-Subgroup;
    preserves-inverses-inclusion-group-Subgroup)
```

## Definitions

### Subsets of abelian groups

```agda
subset-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → UU ((lsuc l) ⊔ l1)
subset-Ab l A = subset-Group l (group-Ab A)

is-set-subset-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → is-set (subset-Ab l A)
is-set-subset-Ab l A = is-set-subset-Group l (group-Ab A)
```

### Subgroups of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A)
  where
  
  contains-zero-subset-Ab : UU l2
  contains-zero-subset-Ab = contains-unit-subset-Group (group-Ab A) P

  is-prop-contains-zero-subset-Ab : is-prop contains-zero-subset-Ab
  is-prop-contains-zero-subset-Ab =
    is-prop-contains-unit-subset-Group (group-Ab A) P

  is-closed-under-add-subset-Ab : UU (l1 ⊔ l2)
  is-closed-under-add-subset-Ab =
    is-closed-under-mul-subset-Group (group-Ab A) P

  is-prop-is-closed-under-add-subset-Ab :
    is-prop is-closed-under-add-subset-Ab
  is-prop-is-closed-under-add-subset-Ab =
    is-prop-is-closed-under-mul-subset-Group (group-Ab A) P

  is-closed-under-neg-subset-Ab : UU (l1 ⊔ l2)
  is-closed-under-neg-subset-Ab =
    is-closed-under-inv-subset-Group (group-Ab A) P

  is-prop-closed-under-neg-subset-Ab :
    is-prop is-closed-under-neg-subset-Ab
  is-prop-closed-under-neg-subset-Ab =
    is-prop-is-closed-under-inv-subset-Group (group-Ab A) P
  
  is-subgroup-Ab : UU (l1 ⊔ l2)
  is-subgroup-Ab = is-subgroup-subset-Group (group-Ab A) P

  is-prop-is-subgroup-Ab : is-prop is-subgroup-Ab
  is-prop-is-subgroup-Ab = is-prop-is-subgroup-subset-Group (group-Ab A) P
```

### The type of all subgroups of an abelian group

```agda
Subgroup-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → UU ((lsuc l) ⊔ l1)
Subgroup-Ab l A = Subgroup l (group-Ab A)

module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where
  
  subset-Subgroup-Ab : subset-Ab l2 A
  subset-Subgroup-Ab = subset-Subgroup (group-Ab A) B

  is-in-Subgroup-Ab : type-Ab A → UU l2
  is-in-Subgroup-Ab = is-in-Subgroup (group-Ab A) B

  is-prop-is-in-Subgroup-Ab :
    (x : type-Ab A) → is-prop (is-in-Subgroup-Ab x)
  is-prop-is-in-Subgroup-Ab =
    is-prop-is-in-Subgroup (group-Ab A) B

  is-subgroup-Subgroup-Ab :
    is-subgroup-Ab A subset-Subgroup-Ab
  is-subgroup-Subgroup-Ab = is-subgroup-Subgroup (group-Ab A) B

  contains-zero-Subgroup-Ab :
    contains-zero-subset-Ab A subset-Subgroup-Ab
  contains-zero-Subgroup-Ab = contains-unit-Subgroup (group-Ab A) B

  is-closed-under-add-Subgroup-Ab :
    is-closed-under-add-subset-Ab A subset-Subgroup-Ab
  is-closed-under-add-Subgroup-Ab = is-closed-under-mul-Subgroup (group-Ab A) B

  is-closed-under-neg-Subgroup-Ab :
    is-closed-under-neg-subset-Ab A subset-Subgroup-Ab
  is-closed-under-neg-Subgroup-Ab = is-closed-under-inv-Subgroup (group-Ab A) B

is-emb-subset-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) → is-emb (subset-Subgroup-Ab {l2 = l2} A)
is-emb-subset-Subgroup-Ab A = is-emb-subset-Subgroup (group-Ab A)
```

### The underlying abelian group of a subgroup of an abelian group

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where
  
  type-ab-Subgroup-Ab : UU (l1 ⊔ l2)
  type-ab-Subgroup-Ab = type-group-Subgroup (group-Ab A) B

  map-inclusion-ab-Subgroup-Ab : type-ab-Subgroup-Ab → type-Ab A
  map-inclusion-ab-Subgroup-Ab = map-inclusion-group-Subgroup (group-Ab A) B

  is-emb-incl-ab-Subgroup-Ab : is-emb map-inclusion-ab-Subgroup-Ab
  is-emb-incl-ab-Subgroup-Ab = is-emb-inclusion-group-Subgroup (group-Ab A) B

  eq-subgroup-ab-eq-ab :
    {x y : type-ab-Subgroup-Ab} →
    Id (map-inclusion-ab-Subgroup-Ab x) (map-inclusion-ab-Subgroup-Ab y) →
    Id x y
  eq-subgroup-ab-eq-ab = eq-subgroup-eq-group (group-Ab A) B

  set-ab-Subgroup-Ab : Set (l1 ⊔ l2)
  set-ab-Subgroup-Ab = set-group-Subgroup (group-Ab A) B

  zero-ab-Subgroup-Ab : type-ab-Subgroup-Ab
  zero-ab-Subgroup-Ab = unit-Subgroup (group-Ab A) B

  add-ab-Subgroup-Ab : (x y : type-ab-Subgroup-Ab) → type-ab-Subgroup-Ab
  add-ab-Subgroup-Ab = mul-Subgroup (group-Ab A) B

  neg-ab-Subgroup-Ab : type-ab-Subgroup-Ab → type-ab-Subgroup-Ab
  neg-ab-Subgroup-Ab = inv-Subgroup (group-Ab A) B

  associative-add-Subgroup-Ab :
    ( x y z : type-ab-Subgroup-Ab) →
    Id (add-ab-Subgroup-Ab (add-ab-Subgroup-Ab x y) z)
       (add-ab-Subgroup-Ab x (add-ab-Subgroup-Ab y z))
  associative-add-Subgroup-Ab =
    associative-mul-Subgroup (group-Ab A) B

  left-unit-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    Id (add-ab-Subgroup-Ab zero-ab-Subgroup-Ab x) x
  left-unit-law-add-Subgroup-Ab =
    left-unit-law-mul-Subgroup (group-Ab A) B

  right-unit-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    Id (add-ab-Subgroup-Ab x zero-ab-Subgroup-Ab) x
  right-unit-law-add-Subgroup-Ab =
    right-unit-law-mul-Subgroup (group-Ab A) B

  left-inverse-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    Id ( add-ab-Subgroup-Ab (neg-ab-Subgroup-Ab x) x)
       ( zero-ab-Subgroup-Ab)
  left-inverse-law-add-Subgroup-Ab =
    left-inverse-law-mul-Subgroup (group-Ab A) B

  right-inverse-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    Id ( add-ab-Subgroup-Ab x (neg-ab-Subgroup-Ab x))
       ( zero-ab-Subgroup-Ab)
  right-inverse-law-add-Subgroup-Ab =
    right-inverse-law-mul-Subgroup (group-Ab A) B

  commutative-add-Subgroup-Ab :
    ( x y : type-ab-Subgroup-Ab) →
    Id ( add-ab-Subgroup-Ab x y) (add-ab-Subgroup-Ab y x)
  commutative-add-Subgroup-Ab x y =
    eq-subgroup-ab-eq-ab (commutative-add-Ab A (pr1 x) (pr1 y))

  semigroup-Subgroup-Ab : Semigroup (l1 ⊔ l2)
  semigroup-Subgroup-Ab = semigroup-Subgroup (group-Ab A) B

  group-Subgroup-Ab : Group (l1 ⊔ l2)
  group-Subgroup-Ab = group-Subgroup (group-Ab A) B

  ab-Subgroup-Ab : Ab (l1 ⊔ l2)
  pr1 ab-Subgroup-Ab = group-Subgroup-Ab
  pr2 ab-Subgroup-Ab = commutative-add-Subgroup-Ab
```

### The inclusion of the underlying group of a subgroup into the ambient abelian group


```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where
  
  preserves-add-inclusion-ab-Subgroup-Ab :
    preserves-add-Ab (ab-Subgroup-Ab A B) A (map-inclusion-ab-Subgroup-Ab A B)
  preserves-add-inclusion-ab-Subgroup-Ab =
    preserves-mul-inclusion-group-Subgroup (group-Ab A) B

  preserves-zero-inclusion-ab-Subgroup-Ab :
    preserves-zero-Ab (ab-Subgroup-Ab A B) A (map-inclusion-ab-Subgroup-Ab A B)
  preserves-zero-inclusion-ab-Subgroup-Ab =
    preserves-unit-inclusion-group-Subgroup (group-Ab A) B

  preserves-negatives-inclusion-ab-Subgroup-Ab :
    preserves-negatives-Ab
      ( ab-Subgroup-Ab A B)
      ( A)
      ( map-inclusion-ab-Subgroup-Ab A B)
  preserves-negatives-inclusion-ab-Subgroup-Ab =
    preserves-inverses-inclusion-group-Subgroup (group-Ab A) B

  inclusion-ab-Subgroup-Ab : type-hom-Ab (ab-Subgroup-Ab A B) A
  inclusion-ab-Subgroup-Ab = inclusion-group-Subgroup (group-Ab A) B
```

### The type of all abelian groups equipped with an embedding into the ambient abelian group

```agda
emb-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) → UU (l1 ⊔ l2)
emb-Ab A B = emb-Group (group-Ab A) (group-Ab B)

emb-Ab-Slice :
  (l : Level) {l1 : Level} (A : Ab l1) → UU ((lsuc l) ⊔ l1)
emb-Ab-Slice l A = emb-Group-Slice l (group-Ab A)

emb-ab-slice-Subgroup-Ab :
  { l1 l2 : Level} (A : Ab l1) →
  Subgroup-Ab l2 A → emb-Ab-Slice (l1 ⊔ l2) A
emb-ab-slice-Subgroup-Ab A = emb-group-slice-Subgroup (group-Ab A)
```
