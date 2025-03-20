# The endomorphism rings of abelian groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.endomorphism-rings-abelian-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.abelian-groups funext
open import group-theory.addition-homomorphisms-abelian-groups funext
open import group-theory.homomorphisms-abelian-groups funext

open import ring-theory.rings funext
```

</details>

## Idea

For any abelian group $A$, the set $\mathrm{hom}(A,A)$ of morphisms of abelian
groups can be equipped with the structure of a ring, where addition is given
pointwise and multiplication is given by composition.

## Definition

### The endomorphism ring on an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  ab-endomorphism-ring-Ab : Ab l
  ab-endomorphism-ring-Ab = ab-hom-Ab A A

  endomorphism-ring-Ab : Ring l
  pr1 endomorphism-ring-Ab = ab-endomorphism-ring-Ab
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
