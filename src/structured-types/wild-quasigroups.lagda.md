# Wild quasigroups

```agda
{-# OPTIONS --lossy-unification #-}

module structured-types.wild-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.equivalences
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets

open import group-theory.quasigroups

open import structured-types.magmas
```

</details>

## Idea

A wild quasigroup is a type `A` equipped with a binary equivalence
`μ : A → A → A`.

## Definition

```agda
Wild-Quasigroup : (l : Level) → UU (lsuc l)
Wild-Quasigroup l = Σ (Magma l) (λ M → is-binary-equiv (mul-Magma M))

module _
  {l : Level} (A : Wild-Quasigroup l)
  where

  magma-Wild-Quasigroup : Magma l
  magma-Wild-Quasigroup = pr1 A

  type-Wild-Quasigroup : UU l
  type-Wild-Quasigroup = type-Magma magma-Wild-Quasigroup

  mul-Wild-Quasigroup : (x y : type-Wild-Quasigroup) → type-Wild-Quasigroup
  mul-Wild-Quasigroup = mul-Magma magma-Wild-Quasigroup

  mul-Wild-Quasigroup' : (x y : type-Wild-Quasigroup) → type-Wild-Quasigroup
  mul-Wild-Quasigroup' x y = mul-Wild-Quasigroup y x

  is-binary-equiv-mul-Wild-Quasigroup :
    is-binary-equiv mul-Wild-Quasigroup
  is-binary-equiv-mul-Wild-Quasigroup = pr2 A

  is-equiv-mul-Wild-Quasigroup :
    (x : type-Wild-Quasigroup) → is-equiv (mul-Wild-Quasigroup x)
  is-equiv-mul-Wild-Quasigroup = pr2 is-binary-equiv-mul-Wild-Quasigroup

  equiv-mul-Wild-Quasigroup : type-Wild-Quasigroup → Aut type-Wild-Quasigroup
  pr1 (equiv-mul-Wild-Quasigroup x) = mul-Wild-Quasigroup x
  pr2 (equiv-mul-Wild-Quasigroup x) = is-equiv-mul-Wild-Quasigroup x

  is-equiv-mul-Wild-Quasigroup' :
    (x : type-Wild-Quasigroup) → is-equiv (mul-Wild-Quasigroup' x)
  is-equiv-mul-Wild-Quasigroup' = pr1 is-binary-equiv-mul-Wild-Quasigroup

  equiv-mul-Wild-Quasigroup' : type-Wild-Quasigroup → Aut type-Wild-Quasigroup
  pr1 (equiv-mul-Wild-Quasigroup' x) = mul-Wild-Quasigroup' x
  pr2 (equiv-mul-Wild-Quasigroup' x) = is-equiv-mul-Wild-Quasigroup' x
```

## Properties

### Wild quasigroups whose underlying type is a [set](foundation-core.sets.md) are precisely [quasigroups](group-theory.quasigroups.md)

```agda
module _
  {l : Level}
  where
  wild-Quasigroup-Quasigroup :
    ( A : Wild-Quasigroup l) → is-set (type-Wild-Quasigroup A) → Quasigroup l
  pr1 (wild-Quasigroup-Quasigroup ((A , _) , _) set-A) = A , set-A
  pr1 (pr2 (wild-Quasigroup-Quasigroup ((A , mul-A) , _) _)) = mul-A
  pr1 (pr2 (pr2 (wild-Quasigroup-Quasigroup
    (( A , mul-A) , equiv-mul-A) _))) x =
      map-section-map-equiv (fix-left mul-A x ,
      is-equiv-fix-left mul-A equiv-mul-A)
  pr1 (pr2 (pr2 (pr2 (wild-Quasigroup-Quasigroup
    (( A , mul-A) , equiv-mul-A) _)))) x =
      map-section-map-equiv ((fix-right mul-A x) ,
      is-equiv-fix-right mul-A equiv-mul-A)
  pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (wild-Quasigroup-Quasigroup
    (( A , mul-A) , (left-equiv-div-A , right-equiv-div-A)) _)))))) x y =
      inv (pr2 (pr1 (right-equiv-div-A x)) y)
  pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (wild-Quasigroup-Quasigroup
    (( A , mul-A) , (left-equiv-div-A , right-equiv-div-A)) _)))))) x y =
      inv (pr2 (pr2 (right-equiv-div-A x)) y) ∙ {!   !}
  pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (wild-Quasigroup-Quasigroup
    (( A , mul-A) , (left-equiv-div-A , right-equiv-div-A)) _)))))) x y =
      inv (pr2 (pr1 (left-equiv-div-A x)) y) ∙ {!   !}
  pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (wild-Quasigroup-Quasigroup
    (( A , mul-A) , (left-equiv-div-A , right-equiv-div-A)) _)))))) x y =
      inv (pr2 (pr2 (left-equiv-div-A x)) y) ∙ {!   !}

  Quasigroup-wild-Quasigroup : Quasigroup l → Wild-Quasigroup l
  pr1 (Quasigroup-wild-Quasigroup ((Q , _) , mul-Q , _)) = Q , mul-Q
  pr2 (Quasigroup-wild-Quasigroup Q) = is-binary-equiv-mul-Quasigroup Q

  abstract
    equiv-wild-Quasigroup-Quasigroup :
      ( Σ (Wild-Quasigroup l) (λ A → is-set (type-Wild-Quasigroup A))) ≃
      Quasigroup l
    pr1 equiv-wild-Quasigroup-Quasigroup (A , set-A) =
      wild-Quasigroup-Quasigroup A set-A
    pr1 (pr1 (pr2 equiv-wild-Quasigroup-Quasigroup)) Q =
      ( Quasigroup-wild-Quasigroup Q) , is-set-Quasigroup Q
    pr2 (pr1 (pr2 equiv-wild-Quasigroup-Quasigroup)) Q = {!   !}
    pr1 (pr2 (pr2 equiv-wild-Quasigroup-Quasigroup)) Q =
      ( Quasigroup-wild-Quasigroup Q) , is-set-Quasigroup Q
    pr2 (pr2 (pr2 equiv-wild-Quasigroup-Quasigroup)) Q = {!   !}
```
