# Symmetric H-spaces

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types.symmetric-h-spaces
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.symmetric-operations funext univalence truncations
open import foundation.universe-levels

open import structured-types.involutive-type-of-h-space-structures funext univalence truncations
open import structured-types.pointed-types
open import structured-types.symmetric-elements-involutive-types funext univalence truncations
```

</details>

## Idea

**Symmetric H-spaces** are [pointed types](structured-types.pointed-types.md)
`A` [equipped](foundation.structure.md) with a symmetric element of the
[involutive type of H-space structures](structured-types.involutive-type-of-h-space-structures.md)
on `A`.

## Definitions

### Symmetric H-space structures on a pointed type

```agda
symmetric-H-Space :
  {l1 : Level} (A : Pointed-Type l1) → UU (lsuc lzero ⊔ l1)
symmetric-H-Space A =
  symmetric-element-Involutive-Type (h-space-Involutive-Type A)
```

### The symmetric binary operation on a symmetric H-space

```agda
symmetric-mul-symmetric-H-Space :
  {l1 : Level} (A : Pointed-Type l1) (μ : symmetric-H-Space A) →
  symmetric-operation (type-Pointed-Type A) (type-Pointed-Type A)
symmetric-mul-symmetric-H-Space A μ (X , f) = pr1 (μ X) f
```
