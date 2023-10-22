# Σ-closed reflective modalities

```agda
module orthogonal-factorization-systems.sigma-closed-reflective-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.reflective-modalities
open import orthogonal-factorization-systems.sigma-closed-modalities
```

</details>

## Idea

A [modality](orthogonal-factorization-systems.modal-operators.md) is **Σ-closed
reflective** if it is
[reflective](orthogonal-factorization-systems.reflective-modalities.md) and
[Σ-closed](orthogonal-factorization-systems.sigma-closed-modalities.md).

## Definition

```agda
is-closed-under-Σ-reflective-modality :
  {l : Level} {○ : operator-modality l l} →
  (unit-○ : unit-modality ○) → UU (lsuc l)
is-closed-under-Σ-reflective-modality unit-○ =
  (is-reflective-modality unit-○) × (is-closed-under-Σ-modality unit-○)

closed-under-Σ-reflective-modality : (l : Level) → UU (lsuc l)
closed-under-Σ-reflective-modality l =
  Σ ( operator-modality l l)
    ( λ ○ →
      Σ ( unit-modality ○)
        ( is-closed-under-Σ-reflective-modality))
```

## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
- [Stable orthogonal factorization systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.md)
