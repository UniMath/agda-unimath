# The infinite dimensional real projective space

```agda
module synthetic-homotopy-theory.infinite-real-projective-space where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.symmetric-concrete-groups

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The {{#concept "infinite dimensional real projective space" Agda=ℝP∞}} `ℝP∞` is
the classifying space of the
[symmetric group](group-theory.symmetric-concrete-groups.md) on a
[two-element type](univalent-combinatorics.2-element-types.md).

## Definitions

### As the delooping of a two-element type

```agda
ℝP∞ : UU (lsuc lzero)
ℝP∞ = classifying-type-symmetric-Concrete-Group (Fin-Set 2)

point-ℝP∞ : ℝP∞
point-ℝP∞ = shape-symmetric-Concrete-Group (Fin-Set 2)
```

### As the sequential colimit of the finite dimensional real projective spaces

The infinite dimensional real projective space `ℝP∞` may be realized as a
[sequential colimit](synthetic-homotopy-theory.sequential-colimits.md) of finite
dimensional real projective spaces, see Section IV {{#cite BR17}}.

```text
  ℝP⁻¹ ──→ ℝP⁰ ──→ ℝP¹ ──→ ℝP² ──→ ⋯ ──→ ℝPⁿ ──→ ℝPⁿ⁺¹ ──→ ⋯ ──→ ℝP∞
```

> This remains to be formalized.

## References

{{#bibliography}}

## See also

- [The infinite dimensional complex projective space](synthetic-homotopy-theory.infinite-complex-projective-space.md)
