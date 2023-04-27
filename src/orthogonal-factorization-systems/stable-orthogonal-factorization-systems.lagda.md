# Stable orthogonal factorization systems

```agda
module orthogonal-factorization-systems.stable-orthogonal-factorization-systems where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.function-classes
open import orthogonal-factorization-systems.wide-function-classes
open import orthogonal-factorization-systems.function-class-factorization-operations
open import orthogonal-factorization-systems.orthogonal-factorization-systems
```

</details>

## Idea

A **stable orthogonal factorization system** is an orthogonal factorization
system whose left class is stable under pullbacks. The right class is in fact
always stable under pullbacks.

## Definition

```agda
is-stable-orthogonal-factorization-system :
  {l1 lL lR : Level} (l2 : Level) →
  orthogonal-factorization-system l1 lL lR → UU (lsuc l1 ⊔ lL ⊔ lsuc l2)
is-stable-orthogonal-factorization-system l2 O =
  is-pullback-stable-function-class l2 (pr1 O)
```

## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.dependent-pair-closed-reflective-subuniverses.md)

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
