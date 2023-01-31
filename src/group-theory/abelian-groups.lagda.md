---
title: Abelian groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.abelian-groups where

open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law using
  (interchange-law-commutative-and-associative)
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.groups using
  ( Group; type-Group; mul-Group; set-Group; is-set-type-Group;
    associative-mul-Group; has-associative-mul-Group; semigroup-Group; is-group;
    is-group-Group; is-unital-Group; unit-Group; left-unit-law-mul-Group;
    right-unit-law-mul-Group; inv-Group; left-inverse-law-mul-Group;
    right-inverse-law-mul-Group; is-group'; has-inverses-Group;
    distributive-inv-mul-Group; mul-Group'; is-equiv-mul-Group;
    is-equiv-mul-Group'; is-binary-equiv-mul-Group; transpose-eq-mul-Group;
    transpose-eq-mul-Group'; is-binary-emb-mul-Group; is-emb-mul-Group;
    is-emb-mul-Group'; is-injective-mul-Group; is-injective-mul-Group';
    is-idempotent-Group; is-unit-is-idempotent-Group; mul-list-Group;
    preserves-concat-mul-list-Group; inv-inv-Group; inv-unit-Group)
open import group-theory.monoids using (is-unital-Semigroup)
open import group-theory.semigroups

open import univalent-combinatorics.lists using (list; concat-list)
```

## Idea

Abelian groups are groups of which the group operation is commutative

## Definition

```agda
is-abelian-group-Prop : {l : Level} → Group l → Prop l
is-abelian-group-Prop G =
  Π-Prop
    ( type-Group G)
    ( λ x →
      Π-Prop
        ( type-Group G)
        ( λ y → Id-Prop (set-Group G) (mul-Group G x y) (mul-Group G y x)))

is-abelian-Group : {l : Level} → Group l → UU l
is-abelian-Group G = type-Prop (is-abelian-group-Prop G)

is-prop-is-abelian-Group :
  {l : Level} (G : Group l) → is-prop (is-abelian-Group G)
is-prop-is-abelian-Group G = is-prop-type-Prop (is-abelian-group-Prop G)

Ab : (l : Level) → UU (lsuc l)
Ab l = Σ (Group l) is-abelian-Group

group-Ab :
  {l : Level} (A : Ab l) → Group l
group-Ab A = pr1 A

set-Ab :
  {l : Level} (A : Ab l) → Set l
set-Ab A = set-Group (group-Ab A)

type-Ab :
  {l : Level} (A : Ab l) → UU l
type-Ab A = type-Group (group-Ab A)

is-set-type-Ab :
  {l : Level} (A : Ab l) → is-set (type-Ab A)
is-set-type-Ab A = is-set-type-Group (group-Ab A)

has-associative-add-Ab :
  {l : Level} (A : Ab l) → has-associative-mul-Set (set-Ab A)
has-associative-add-Ab A = has-associative-mul-Group (group-Ab A)

add-Ab :
  {l : Level} (A : Ab l) → type-Ab A → type-Ab A → type-Ab A
add-Ab A = mul-Group (group-Ab A)

add-Ab' :
  {l : Level} (A : Ab l) → type-Ab A → type-Ab A → type-Ab A
add-Ab' A = mul-Group' (group-Ab A)

ap-add-Ab :
  {l : Level} (A : Ab l) {x y x' y' : type-Ab A} (p : Id x x') (q : Id y y') →
  Id (add-Ab A x y) (add-Ab A x' y')
ap-add-Ab A p q = ap-binary (add-Ab A) p q

associative-add-Ab :
  {l : Level} (A : Ab l) (x y z : type-Ab A) →
  Id (add-Ab A (add-Ab A x y) z) (add-Ab A x (add-Ab A y z))
associative-add-Ab A = associative-mul-Group (group-Ab A)

semigroup-Ab :
  {l : Level} (A : Ab l) → Semigroup l
semigroup-Ab A = semigroup-Group (group-Ab A)

is-group-Ab :
  {l : Level} (A : Ab l) → is-group (semigroup-Ab A)
is-group-Ab A = is-group-Group (group-Ab A)

has-zero-Ab :
  {l : Level} (A : Ab l) → is-unital-Semigroup (semigroup-Ab A)
has-zero-Ab A = is-unital-Group (group-Ab A)

zero-Ab :
  {l : Level} (A : Ab l) → type-Ab A
zero-Ab A = unit-Group (group-Ab A)

is-zero-Ab : {l : Level} (A : Ab l) → type-Ab A → UU l
is-zero-Ab A x = Id x (zero-Ab A)

left-unit-law-add-Ab :
  {l : Level} (A : Ab l) → (x : type-Ab A) →
  Id (add-Ab A (zero-Ab A) x) x
left-unit-law-add-Ab A = left-unit-law-mul-Group (group-Ab A)

right-unit-law-add-Ab :
  {l : Level} (A : Ab l) → (x : type-Ab A) →
  Id (add-Ab A x (zero-Ab A)) x
right-unit-law-add-Ab A = right-unit-law-mul-Group (group-Ab A)

has-negatives-Ab :
  {l : Level} (A : Ab l) → is-group' (semigroup-Ab A) (has-zero-Ab A)
has-negatives-Ab A = has-inverses-Group (group-Ab A)

neg-Ab :
  {l : Level} (A : Ab l) → type-Ab A → type-Ab A
neg-Ab A = inv-Group (group-Ab A)

left-inverse-law-add-Ab :
  {l : Level} (A : Ab l) (x : type-Ab A) →
  Id (add-Ab A (neg-Ab A x) x) (zero-Ab A)
left-inverse-law-add-Ab A = left-inverse-law-mul-Group (group-Ab A)

right-inverse-law-add-Ab :
  {l : Level} (A : Ab l) (x : type-Ab A) →
  Id (add-Ab A x (neg-Ab A x)) (zero-Ab A)
right-inverse-law-add-Ab A = right-inverse-law-mul-Group (group-Ab A)

commutative-add-Ab :
  {l : Level} (A : Ab l) (x y : type-Ab A) →
  Id (add-Ab A x y) (add-Ab A y x)
commutative-add-Ab A = pr2 A

interchange-add-add-Ab :
  {l : Level} (A : Ab l) (a b c d : type-Ab A) →
  Id ( add-Ab A (add-Ab A a b) (add-Ab A c d))
     ( add-Ab A (add-Ab A a c) (add-Ab A b d))
interchange-add-add-Ab A =
  interchange-law-commutative-and-associative
    ( add-Ab A)
    ( commutative-add-Ab A)
    ( associative-add-Ab A)

distributive-neg-add-Ab :
  {l : Level} (A : Ab l) (x y : type-Ab A) →
  Id (neg-Ab A (add-Ab A x y)) (add-Ab A (neg-Ab A x) (neg-Ab A y))
distributive-neg-add-Ab A x y =
  ( distributive-inv-mul-Group (group-Ab A) x y) ∙
  ( commutative-add-Ab A (neg-Ab A y) (neg-Ab A x))

neg-neg-Ab :
  {l : Level} (A : Ab l) (x : type-Ab A) → neg-Ab A (neg-Ab A x) ＝ x
neg-neg-Ab A = inv-inv-Group (group-Ab A)

neg-zero-Ab : {l : Level} (A : Ab l) → neg-Ab A (zero-Ab A) ＝ zero-Ab A
neg-zero-Ab A = inv-unit-Group (group-Ab A)
```

### Addition on an abelian group is a binary equivalence

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-equiv-add-Ab : (x : type-Ab A) → is-equiv (add-Ab A x)
  is-equiv-add-Ab = is-equiv-mul-Group (group-Ab A)

  is-equiv-add-Ab' : (x : type-Ab A) → is-equiv (add-Ab' A x)
  is-equiv-add-Ab' = is-equiv-mul-Group' (group-Ab A)

  is-binary-equiv-add-Ab : is-binary-equiv (add-Ab A)
  is-binary-equiv-add-Ab = is-binary-equiv-mul-Group (group-Ab A)
```

### Addition on an abelian group is a binary embedding

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-binary-emb-add-Ab : is-binary-emb (add-Ab A)
  is-binary-emb-add-Ab = is-binary-emb-mul-Group (group-Ab A)

  is-emb-add-Ab : (x : type-Ab A) → is-emb (add-Ab A x)
  is-emb-add-Ab = is-emb-mul-Group (group-Ab A)

  is-emb-add-Ab' : (x : type-Ab A) → is-emb (add-Ab' A x)
  is-emb-add-Ab' = is-emb-mul-Group' (group-Ab A)
```

### Addition on an abelian group is pointwise injective from both sides

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-injective-add-Ab : (x : type-Ab A) → is-injective (add-Ab A x)
  is-injective-add-Ab = is-injective-mul-Group (group-Ab A)

  is-injective-add-Ab' : (x : type-Ab A) → is-injective (add-Ab' A x)
  is-injective-add-Ab' = is-injective-mul-Group' (group-Ab A)
```

### Transposing identifications in abelian groups

```agda
module _
  {l : Level} (A : Ab l)
  where

  transpose-eq-add-Ab :
    {x y z : type-Ab A} → Id (add-Ab A x y) z → Id x (add-Ab A z (neg-Ab A y))
  transpose-eq-add-Ab = transpose-eq-mul-Group (group-Ab A)

  transpose-eq-add-Ab' :
    {x y z : type-Ab A} → Id (add-Ab A x y) z → Id y (add-Ab A (neg-Ab A x) z)
  transpose-eq-add-Ab' = transpose-eq-mul-Group' (group-Ab A)
```

### Any idempotent element in an abelian group is zero

```agda
module _
  {l : Level} (A : Ab l)
  where
  
  is-idempotent-Ab : type-Ab A → UU l
  is-idempotent-Ab = is-idempotent-Group (group-Ab A)

  is-zero-is-idempotent-Ab :
    {x : type-Ab A} → is-idempotent-Ab x → is-zero-Ab A x
  is-zero-is-idempotent-Ab = is-unit-is-idempotent-Group (group-Ab A)
```

### Addition of a list of elements in an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where
  
  add-list-Ab : list (type-Ab A) → type-Ab A
  add-list-Ab = mul-list-Group (group-Ab A)

  preserves-concat-add-list-Ab :
    (l1 l2 : list (type-Ab A)) →
    Id ( add-list-Ab (concat-list l1 l2))
       ( add-Ab A (add-list-Ab l1) (add-list-Ab l2))
  preserves-concat-add-list-Ab = preserves-concat-mul-list-Group (group-Ab A)
```
