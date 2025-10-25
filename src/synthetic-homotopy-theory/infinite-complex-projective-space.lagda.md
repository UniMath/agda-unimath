# The infinite dimensional complex projective space

```agda
module synthetic-homotopy-theory.infinite-complex-projective-space where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.set-truncations
open import foundation.universe-levels

open import synthetic-homotopy-theory.circle
```

</details>

## Definitions

### `ℂP∞` as the `1`-connected component of the universe at the circle

```agda
ℂP∞ : UU (lsuc lzero)
ℂP∞ = Σ (UU lzero) (λ X → type-trunc-Set (𝕊¹ ≃ X))

point-ℂP∞ : ℂP∞
pr1 point-ℂP∞ = 𝕊¹
pr2 point-ℂP∞ = unit-trunc-Set id-equiv
```

### `ℂP∞` as the `2`-truncation of the `2`-sphere

This remains to be defined.
[#742](https://github.com/UniMath/agda-unimath/issues/742)

## See also

- [The infinite dimensional real projective space](synthetic-homotopy-theory.infinite-real-projective-space.md)
