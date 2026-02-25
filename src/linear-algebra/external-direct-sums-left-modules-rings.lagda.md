# External direct sums of left modules over rings

```agda
module linear-algebra.external-direct-sums-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.external-direct-sums-abelian-groups

open import linear-algebra.dependent-products-left-modules-rings
open import linear-algebra.left-modules-rings
open import linear-algebra.left-submodules-rings
open import linear-algebra.subsets-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

The external
{{#concept "direct sum" WDID=Q13582243 WD="direct sum" Disambiguation="of a family of left modules over a ring" Agda=∑-left-module-Ring}}
of a family of [left modules](linear-algebra.left-modules-rings.md) `Mᵢ` indexed
by a type `I` over a [ring](ring-theory.rings.md) `R` is the
[submodule](linear-algebra.left-submodules-rings.md) of the
[dependent product](linear-algebra.dependent-products-left-modules-rings.md) of
the `Mᵢ` containing those elements `f : I → Mᵢ` such that `f` is zero except
possibly on a
[finitely enumerable subtype](univalent-combinatorics.finitely-enumerable-subtypes.md)
of `I`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (I : UU l2)
  (M : I → left-module-Ring l3 R)
  where

  has-finite-support-prop-type-Π-left-module-Ring :
    subtype (lsuc l2 ⊔ l3) (type-Π-left-module-Ring R I M)
  has-finite-support-prop-type-Π-left-module-Ring =
    has-finite-support-prop-type-Π-Ab I (λ i → ab-left-module-Ring R (M i))

  has-finite-support-type-Π-left-module-Ring :
    type-Π-left-module-Ring R I M → UU (lsuc l2 ⊔ l3)
  has-finite-support-type-Π-left-module-Ring =
    is-in-subtype has-finite-support-prop-type-Π-left-module-Ring

  abstract
    is-closed-under-addition-has-finite-support-type-Π-left-module-Ring :
      is-closed-under-addition-subset-left-module-Ring
        ( R)
        ( Π-left-module-Ring R I M)
        ( has-finite-support-prop-type-Π-left-module-Ring)
    is-closed-under-addition-has-finite-support-type-Π-left-module-Ring x y =
      is-closed-under-addition-has-finite-support-type-Π-Ab
        ( I)
        ( λ i → ab-left-module-Ring R (M i))

    has-finite-support-zero-Π-left-module-Ring :
      has-finite-support-type-Π-left-module-Ring
        ( zero-Π-left-module-Ring R I M)
    has-finite-support-zero-Π-left-module-Ring =
      has-finite-support-zero-Π-Ab
        ( I)
        ( λ i → ab-left-module-Ring R (M i))

    is-closed-under-scalar-multiplication-has-finite-support-type-Π-left-module-Ring :
      is-closed-under-scalar-multiplication-subset-left-module-Ring
        ( R)
        ( Π-left-module-Ring R I M)
        ( has-finite-support-prop-type-Π-left-module-Ring)
    is-closed-under-scalar-multiplication-has-finite-support-type-Π-left-module-Ring
      r f =
      map-trunc-Prop
        ( λ (Ff , Hf) →
          ( Ff ,
            λ i →
              map-disjunction
                ( id)
                ( λ fi=0 →
                  ( ap (mul-left-module-Ring R (M i) r) fi=0) ∙
                  ( right-zero-law-mul-left-module-Ring R (M i) r))
                ( Hf i)))

  submodule-has-finite-support-Π-left-module-Ring :
    left-submodule-Ring (lsuc l2 ⊔ l3) R (Π-left-module-Ring R I M)
  submodule-has-finite-support-Π-left-module-Ring =
    ( has-finite-support-prop-type-Π-left-module-Ring ,
      has-finite-support-zero-Π-left-module-Ring ,
      is-closed-under-addition-has-finite-support-type-Π-left-module-Ring ,
      is-closed-under-scalar-multiplication-has-finite-support-type-Π-left-module-Ring)

  ∑-left-module-Ring : left-module-Ring (lsuc l2 ⊔ l3) R
  ∑-left-module-Ring =
    left-module-left-submodule-Ring
      ( R)
      ( Π-left-module-Ring R I M)
      ( submodule-has-finite-support-Π-left-module-Ring)

  type-∑-left-module-Ring : UU (lsuc l2 ⊔ l3)
  type-∑-left-module-Ring = type-left-module-Ring R ∑-left-module-Ring
```

## Properties

### The map of dependent pairs into the direct sum

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (I : Set l2)
  (D : has-decidable-equality (type-Set I))
  (M : type-Set I → left-module-Ring l3 R)
  where

  in-pair-∑-left-module-Ring :
    Σ (type-Set I) (type-left-module-Ring R ∘ M) →
    type-∑-left-module-Ring R (type-Set I) M
  in-pair-∑-left-module-Ring =
    in-pair-∑-Ab
      ( I)
      ( D)
      ( ab-left-module-Ring R ∘ M)
```

## External links

- [Direct sum of modules](https://en.wikipedia.org/wiki/Direct_sum_of_modules)
  on Wikipedia
