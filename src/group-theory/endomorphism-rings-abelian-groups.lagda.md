---
title: The endomorphism rings of abelian groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.endomorphism-rings-abelian-groups where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (Level)

open import group-theory.abelian-groups using (Ab)
open import group-theory.addition-homomorphisms-abelian-groups using
  ( add-hom-Ab; zero-hom-Ab; neg-hom-Ab; associative-add-hom-Ab;
    left-unit-law-add-hom-Ab; right-unit-law-add-hom-Ab;
    left-inverse-law-add-hom-Ab; right-inverse-law-add-hom-Ab;
    commutative-add-hom-Ab; left-distributive-comp-add-hom-Ab;
    right-distributive-comp-add-hom-Ab)
open import group-theory.homomorphisms-abelian-groups using
  ( type-hom-Ab; hom-Ab; comp-hom-Ab; associative-comp-hom-Ab; id-hom-Ab;
    left-unit-law-comp-hom-Ab; right-unit-law-comp-hom-Ab)

open import ring-theory.rings using (Ring)
```

## Idea

For any abelian group $A$, the set $\mathrm{hom}(A,A)$ of morphisms of abelian groups can be equipped with the structure of a ring, where addition is given pointwise and multiplication is given by composition.

## Definition

### The endomorphism ring on an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where
  
  endomorphism-ring-Ab : Ring l
  pr1 (pr1 (pr1 (pr1 endomorphism-ring-Ab))) = hom-Ab A A
  pr1 (pr2 (pr1 (pr1 (pr1 endomorphism-ring-Ab)))) = add-hom-Ab A A
  pr2 (pr2 (pr1 (pr1 (pr1 endomorphism-ring-Ab)))) = associative-add-hom-Ab A A
  pr1 (pr1 (pr2 (pr1 (pr1 endomorphism-ring-Ab)))) = zero-hom-Ab A A
  pr1 (pr2 (pr1 (pr2 (pr1 (pr1 endomorphism-ring-Ab))))) =
    left-unit-law-add-hom-Ab A A
  pr2 (pr2 (pr1 (pr2 (pr1 (pr1 endomorphism-ring-Ab))))) =
    right-unit-law-add-hom-Ab A A
  pr1 (pr2 (pr2 (pr1 (pr1 endomorphism-ring-Ab)))) = neg-hom-Ab A A
  pr1 (pr2 (pr2 (pr2 (pr1 (pr1 endomorphism-ring-Ab))))) =
    left-inverse-law-add-hom-Ab A A
  pr2 (pr2 (pr2 (pr2 (pr1 (pr1 endomorphism-ring-Ab))))) =
    right-inverse-law-add-hom-Ab A A
  pr2 (pr1 endomorphism-ring-Ab) = commutative-add-hom-Ab A A
  pr1 (pr1 (pr2 endomorphism-ring-Ab)) = comp-hom-Ab A A A
  pr2 (pr1 (pr2 endomorphism-ring-Ab)) = associative-comp-hom-Ab A A A A
  pr1 (pr1 (pr2 (pr2 endomorphism-ring-Ab))) = id-hom-Ab A
  pr1 (pr2 (pr1 (pr2 (pr2 endomorphism-ring-Ab)))) =
    left-unit-law-comp-hom-Ab A A
  pr2 (pr2 (pr1 (pr2 (pr2 endomorphism-ring-Ab)))) =
    right-unit-law-comp-hom-Ab A A
  pr1 (pr2 (pr2 (pr2 endomorphism-ring-Ab))) =
    left-distributive-comp-add-hom-Ab A A A
  pr2 (pr2 (pr2 (pr2 endomorphism-ring-Ab))) =
    right-distributive-comp-add-hom-Ab A A A
```
