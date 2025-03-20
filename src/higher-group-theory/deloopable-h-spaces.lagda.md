# Deloopable H-spaces

```agda
open import foundation.function-extensionality-axiom

module
  higher-group-theory.deloopable-h-spaces
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import higher-group-theory.higher-groups funext

open import structured-types.equivalences-h-spaces funext
open import structured-types.h-spaces funext
```

</details>

## Idea

Consider an [H-space](structured-types.h-spaces.md) with underlying
[pointed type](structured-types.pointed-types.md) `(X , *)` and with
multiplication `μ` satisfying

```text
   left-unit-law : (x : X) → μ * x ＝ x
  right-unit-law : (x : X) → μ x * ＝ x
    coh-unit-law : left-unit-law * ＝ right-unit-law *.
```

A {{#concept "delooping" Disambiguation="H-space" Agda=delooping-H-Space}} of
the H-space `X` consists of an [∞-group](higher-group-theory.higher-groups.md)
`G` and an [equivalence of H-spaces](structured-types.equivalences-h-spaces.md)

```text
  X ≃ h-space-∞-Group G.
```

## Definitions

### Deloopings of H-spaces of a given universe level

```agda
module _
  {l1 : Level} (l2 : Level) (A : H-Space l1)
  where

  delooping-H-Space-Level : UU (l1 ⊔ lsuc l2)
  delooping-H-Space-Level =
    Σ (∞-Group l2) (λ G → equiv-H-Space A (h-space-∞-Group G))
```

### Deloopings of H-spaces

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  delooping-H-Space : UU (lsuc l1)
  delooping-H-Space = delooping-H-Space-Level l1 A
```

## See also

- [Deloopable groups](higher-group-theory.deloopable-groups.md)
