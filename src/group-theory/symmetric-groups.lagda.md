# Symmetric groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.symmetric-groups where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _∘e_; associative-comp-equiv; id-equiv; left-unit-law-equiv; inv-equiv;
    right-unit-law-equiv; left-inverse-law-equiv; right-inverse-law-equiv)
open import foundation.sets using
  ( UU-Set; type-Set; is-set; is-set-type-Set; aut-Set)
open import foundation.universe-levels using (Level; UU)

open import group-theory.groups using (is-group'; Group)
open import group-theory.monoids using (is-unital)
open import group-theory.semigroups using (has-associative-mul-Set; Semigroup)
```

```agda
set-symmetric-Group : {l : Level} (X : UU-Set l) → UU-Set l
set-symmetric-Group X = aut-Set X

type-symmetric-Group : {l : Level} (X : UU-Set l) → UU l
type-symmetric-Group X = type-Set (set-symmetric-Group X)

is-set-type-symmetric-Group :
  {l : Level} (X : UU-Set l) → is-set (type-symmetric-Group X)
is-set-type-symmetric-Group X = is-set-type-Set (set-symmetric-Group X)

has-associative-mul-aut-Set :
  {l : Level} (X : UU-Set l) → has-associative-mul-Set (aut-Set X)
pr1 (has-associative-mul-aut-Set X) f e = f ∘e e
pr2 (has-associative-mul-aut-Set X) e f g = associative-comp-equiv g f e

symmetric-Semigroup :
  {l : Level} (X : UU-Set l) → Semigroup l
pr1 (symmetric-Semigroup X) = set-symmetric-Group X
pr2 (symmetric-Semigroup X) = has-associative-mul-aut-Set X

is-unital-symmetric-Semigroup :
  {l : Level} (X : UU-Set l) → is-unital (symmetric-Semigroup X)
pr1 (is-unital-symmetric-Semigroup X) = id-equiv
pr1 (pr2 (is-unital-symmetric-Semigroup X)) = left-unit-law-equiv
pr2 (pr2 (is-unital-symmetric-Semigroup X)) = right-unit-law-equiv

is-group-symmetric-Semigroup' :
  {l : Level} (X : UU-Set l) →
  is-group' (symmetric-Semigroup X) (is-unital-symmetric-Semigroup X)
pr1 (is-group-symmetric-Semigroup' X) = inv-equiv
pr1 (pr2 (is-group-symmetric-Semigroup' X)) = left-inverse-law-equiv
pr2 (pr2 (is-group-symmetric-Semigroup' X)) = right-inverse-law-equiv

symmetric-Group :
  {l : Level} → UU-Set l → Group l
pr1 (symmetric-Group X) = symmetric-Semigroup X
pr1 (pr2 (symmetric-Group X)) = is-unital-symmetric-Semigroup X
pr2 (pr2 (symmetric-Group X)) = is-group-symmetric-Semigroup' X
```
