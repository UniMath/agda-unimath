# Wild loops

```agda
module structured-types.wild-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.pointed-types
open import structured-types.wild-quasigroups
```

</details>

## Idea

A wild loop is a wild quasigroup equipped with a unit element.

## Definition

```agda
Wild-Loop : (l : Level) → UU (lsuc l)
Wild-Loop l =
  Σ (H-Space l) (λ M → is-binary-equiv (mul-H-Space M))

module _
  {l : Level} (L : Wild-Loop l)
  where

  h-space-Wild-Loop : H-Space l
  h-space-Wild-Loop = pr1 L

  pointed-type-Wild-Loop : Pointed-Type l
  pointed-type-Wild-Loop =
    pointed-type-H-Space h-space-Wild-Loop

  type-Wild-Loop : UU l
  type-Wild-Loop = type-H-Space h-space-Wild-Loop

  unit-Wild-Loop : type-Wild-Loop
  unit-Wild-Loop = unit-H-Space h-space-Wild-Loop

  unital-mul-Wild-Loop : coherent-unital-mul-Pointed-Type pointed-type-Wild-Loop
  unital-mul-Wild-Loop =
    coherent-unital-mul-H-Space h-space-Wild-Loop

  mul-Wild-Loop : type-Wild-Loop → type-Wild-Loop → type-Wild-Loop
  mul-Wild-Loop = mul-H-Space h-space-Wild-Loop

  mul-Wild-Loop' : type-Wild-Loop → type-Wild-Loop → type-Wild-Loop
  mul-Wild-Loop' = mul-H-Space' h-space-Wild-Loop

  ap-mul-Wild-Loop :
    {a b c d : type-Wild-Loop} → a ＝ b → c ＝ d →
    Id (mul-Wild-Loop a c) (mul-Wild-Loop b d)
  ap-mul-Wild-Loop = ap-mul-H-Space h-space-Wild-Loop

  magma-Wild-Loop : Magma l
  magma-Wild-Loop = magma-H-Space h-space-Wild-Loop

  left-unit-law-mul-Wild-Loop :
    (x : type-Wild-Loop) → Id (mul-Wild-Loop unit-Wild-Loop x) x
  left-unit-law-mul-Wild-Loop =
    left-unit-law-mul-H-Space h-space-Wild-Loop

  right-unit-law-mul-Wild-Loop :
    (x : type-Wild-Loop) → Id (mul-Wild-Loop x unit-Wild-Loop) x
  right-unit-law-mul-Wild-Loop =
    right-unit-law-mul-H-Space h-space-Wild-Loop

  coh-unit-laws-mul-Wild-Loop :
    Id
      ( left-unit-law-mul-Wild-Loop unit-Wild-Loop)
      ( right-unit-law-mul-Wild-Loop unit-Wild-Loop)
  coh-unit-laws-mul-Wild-Loop =
    coh-unit-laws-mul-H-Space h-space-Wild-Loop

  is-binary-equiv-mul-Wild-Loop : is-binary-equiv mul-Wild-Loop
  is-binary-equiv-mul-Wild-Loop = pr2 L

  wild-quasigroup-Wild-Loop : Wild-Quasigroup l
  pr1 wild-quasigroup-Wild-Loop = magma-Wild-Loop
  pr2 wild-quasigroup-Wild-Loop = is-binary-equiv-mul-Wild-Loop

  is-equiv-mul-Wild-Loop : (x : type-Wild-Loop) → is-equiv (mul-Wild-Loop x)
  is-equiv-mul-Wild-Loop = pr2 is-binary-equiv-mul-Wild-Loop

  equiv-mul-Wild-Loop : type-Wild-Loop → Aut type-Wild-Loop
  equiv-mul-Wild-Loop = equiv-mul-Wild-Quasigroup wild-quasigroup-Wild-Loop

  is-equiv-mul-Wild-Loop' : (x : type-Wild-Loop) → is-equiv (mul-Wild-Loop' x)
  is-equiv-mul-Wild-Loop' = pr1 is-binary-equiv-mul-Wild-Loop

  equiv-mul-Wild-Loop' : type-Wild-Loop → Aut type-Wild-Loop
  equiv-mul-Wild-Loop' = equiv-mul-Wild-Quasigroup' wild-quasigroup-Wild-Loop
```
