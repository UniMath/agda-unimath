# Wild quasigroups

```agda
module structured-types.wild-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import structured-types.magmas
```

</details>

## Idea

A {{#concept "wild quasigroup" Agda=Wild-Quasigroup}} is a type `A`
[equipped](foundation.structure.md) with a
[binary equivalence](foundation.binary-equivalences.md) `μ : A → A → A`.

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
