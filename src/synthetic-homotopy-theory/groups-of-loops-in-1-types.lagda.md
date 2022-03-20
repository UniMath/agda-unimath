# Groups of loops in 1-types

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.groups-of-loops-in-1-types where

open import foundation.1-types using
  ( UU-1-Type; type-1-Type; is-1-type-type-1-Type)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using
  ( _∙_; assoc; refl; left-unit; right-unit; left-inv; right-inv; inv)
open import foundation.sets using (is-set; UU-Set)
open import foundation.universe-levels using (Level; UU)

open import group-theory.groups using (Group)
open import group-theory.semigroups using (Semigroup)

open import synthetic-homotopy-theory.loop-spaces using (type-Ω)
open import synthetic-homotopy-theory.pointed-types using (Pointed-Type)
```

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where
  
  loop-space-Set : is-set (type-Ω A) → UU-Set l
  pr1 (loop-space-Set is-set-Ω) = type-Ω A
  pr2 (loop-space-Set is-set-Ω) = is-set-Ω

  loop-space-Semigroup : is-set (type-Ω A) → Semigroup l
  pr1 (loop-space-Semigroup is-set-Ω) = loop-space-Set is-set-Ω
  pr1 (pr2 (loop-space-Semigroup is-set-Ω)) p q = p ∙ q
  pr2 (pr2 (loop-space-Semigroup is-set-Ω)) = assoc

  loop-space-Group : is-set (type-Ω A) → Group l
  pr1 (loop-space-Group is-set-Ω) = loop-space-Semigroup is-set-Ω
  pr1 (pr1 (pr2 (loop-space-Group is-set-Ω))) = refl
  pr1 (pr2 (pr1 (pr2 (loop-space-Group is-set-Ω)))) q = left-unit
  pr2 (pr2 (pr1 (pr2 (loop-space-Group is-set-Ω)))) p = right-unit
  pr1 (pr2 (pr2 (loop-space-Group is-set-Ω))) = inv
  pr1 (pr2 (pr2 (pr2 (loop-space-Group is-set-Ω)))) = left-inv
  pr2 (pr2 (pr2 (pr2 (loop-space-Group is-set-Ω)))) = right-inv

loop-space-1-type-Set :
  {l : Level} (A : UU-1-Type l) (a : type-1-Type A) → UU-Set l
loop-space-1-type-Set A a =
  loop-space-Set (pair (type-1-Type A) a) (is-1-type-type-1-Type A a a)

loop-space-1-type-Semigroup :
  {l : Level} (A : UU-1-Type l) (a : type-1-Type A) → Semigroup l
loop-space-1-type-Semigroup A a =
  loop-space-Semigroup (pair (type-1-Type A) a) (is-1-type-type-1-Type A a a)

loop-space-1-type-Group :
  {l : Level} (A : UU-1-Type l) (a : type-1-Type A) → Group l
loop-space-1-type-Group A a =
  loop-space-Group (pair (type-1-Type A) a) (is-1-type-type-1-Type A a a)
```
