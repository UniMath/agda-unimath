# Abelian groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.abelian-groups where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositions using (is-prop; is-prop-Π)
open import foundation.sets using (UU-Set; is-set)
open import foundation.universe-levels using (Level; UU; lsuc)

open import group-theory.groups using
  ( Group; type-Group; mul-Group; set-Group; is-set-type-Group;
    associative-mul-Group; assoc-mul-Group; semigroup-Group; is-group;
    is-group-Group; is-unital-Group; unit-Group; left-unit-law-Group;
    right-unit-law-Group; inv-Group; left-inverse-law-Group;
    right-inverse-law-Group; is-group'; has-inverses-Group)
open import group-theory.monoids using (is-unital)
open import group-theory.semigroups using
  ( has-associative-mul-Set; Semigroup)
```

## Idea

Abelian groups are groups of which the group operation is commutative

## Definition

```agda
is-abelian-Group :
  {l : Level} (G : Group l) → UU l
is-abelian-Group G =
  (x y : type-Group G) → Id (mul-Group G x y) (mul-Group G y x)

Ab : (l : Level) → UU (lsuc l)
Ab l = Σ (Group l) is-abelian-Group

group-Ab :
  {l : Level} (A : Ab l) → Group l
group-Ab A = pr1 A

set-Ab :
  {l : Level} (A : Ab l) → UU-Set l
set-Ab A = set-Group (group-Ab A)

type-Ab :
  {l : Level} (A : Ab l) → UU l
type-Ab A = type-Group (group-Ab A)

is-set-type-Ab :
  {l : Level} (A : Ab l) → is-set (type-Ab A)
is-set-type-Ab A = is-set-type-Group (group-Ab A)

associative-add-Ab :
  {l : Level} (A : Ab l) → has-associative-mul-Set (set-Ab A)
associative-add-Ab A = associative-mul-Group (group-Ab A)

add-Ab :
  {l : Level} (A : Ab l) → type-Ab A → type-Ab A → type-Ab A
add-Ab A = mul-Group (group-Ab A)

assoc-add-Ab :
  {l : Level} (A : Ab l) (x y z : type-Ab A) →
  Id (add-Ab A (add-Ab A x y) z) (add-Ab A x (add-Ab A y z))
assoc-add-Ab A = assoc-mul-Group (group-Ab A)

semigroup-Ab :
  {l : Level} (A : Ab l) → Semigroup l
semigroup-Ab A = semigroup-Group (group-Ab A)

is-group-Ab :
  {l : Level} (A : Ab l) → is-group (semigroup-Ab A)
is-group-Ab A = is-group-Group (group-Ab A)

has-zero-Ab :
  {l : Level} (A : Ab l) → is-unital (semigroup-Ab A)
has-zero-Ab A = is-unital-Group (group-Ab A)

zero-Ab :
  {l : Level} (A : Ab l) → type-Ab A
zero-Ab A = unit-Group (group-Ab A)

left-zero-law-Ab :
  {l : Level} (A : Ab l) → (x : type-Ab A) →
  Id (add-Ab A (zero-Ab A) x) x
left-zero-law-Ab A = left-unit-law-Group (group-Ab A)

right-zero-law-Ab :
  {l : Level} (A : Ab l) → (x : type-Ab A) →
  Id (add-Ab A x (zero-Ab A)) x
right-zero-law-Ab A = right-unit-law-Group (group-Ab A)

has-negatives-Ab :
  {l : Level} (A : Ab l) → is-group' (semigroup-Ab A) (has-zero-Ab A)
has-negatives-Ab A = has-inverses-Group (group-Ab A)

neg-Ab :
  {l : Level} (A : Ab l) → type-Ab A → type-Ab A
neg-Ab A = inv-Group (group-Ab A)

left-negative-law-Ab :
  {l : Level} (A : Ab l) (x : type-Ab A) →
  Id (add-Ab A (neg-Ab A x) x) (zero-Ab A)
left-negative-law-Ab A = left-inverse-law-Group (group-Ab A)

right-negative-law-Ab :
  {l : Level} (A : Ab l) (x : type-Ab A) →
  Id (add-Ab A x (neg-Ab A x)) (zero-Ab A)
right-negative-law-Ab A = right-inverse-law-Group (group-Ab A)

is-commutative-add-Ab :
  {l : Level} (A : Ab l) (x y : type-Ab A) →
  Id (add-Ab A x y) (add-Ab A y x)
is-commutative-add-Ab A = pr2 A

{- So far the basic interface of abelian groups -}

is-prop-is-abelian-Group :
  {l : Level} (G : Group l) → is-prop (is-abelian-Group G)
is-prop-is-abelian-Group G =
  is-prop-Π (λ x → is-prop-Π (λ y → is-set-type-Group G _ _))
```
