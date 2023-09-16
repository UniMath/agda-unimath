# Σ-closed modalities

```agda
module orthogonal-factorization-systems.sigma-closed-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.sigma-closed-subuniverses
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

A [modal operator](orthogonal-factorization-systems.modal-operators.md) with
unit is **Σ-closed** if its [subuniverse](foundation.subuniverses.md) of modal
types is [Σ-closed](foundation.sigma-closed-subuniverses.md). I.e. if `Σ A B` is
modal whenever `B` is a family of modal types over modal base `A`.

## Definition

```agda
is-closed-under-Σ-modality :
  {l : Level} {○ : operator-modality l l} → unit-modality ○ → UU (lsuc l)
is-closed-under-Σ-modality =
  is-closed-under-Σ-subuniverse ∘ modal-type-subuniverse

closed-under-Σ-modality : (l : Level) → UU (lsuc l)
closed-under-Σ-modality l =
  Σ ( operator-modality l l)
    ( λ ○ → Σ (unit-modality ○) (is-closed-under-Σ-modality))
```

## See also

- [Reflective modalities](orthogonal-factorization-systems.reflective-modalities.md)
