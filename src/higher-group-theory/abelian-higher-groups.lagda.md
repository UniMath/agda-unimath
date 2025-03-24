# Abelian higher groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module higher-group-theory.abelian-higher-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.small-types funext univalence truncations
open import foundation.universe-levels

open import higher-group-theory.equivalences-higher-groups funext univalence truncations
open import higher-group-theory.higher-groups funext univalence truncations
open import higher-group-theory.small-higher-groups funext univalence truncations

open import structured-types.pointed-equivalences funext univalence truncations
open import structured-types.pointed-types
open import structured-types.small-pointed-types funext univalence truncations

open import synthetic-homotopy-theory.connective-spectra funext univalence truncations
```

</details>

## Idea

An {{#concept "abelian" Disambiguation="∞-group"}}, or
{{#concept "commutative" Disambiguation="∞-group"}} ∞-group is a
[higher group](higher-group-theory.higher-groups.md) `A₀` that is commutative in
a fully coherent way. There are multiple ways to express this in Homotopy Type
Theory. One way is to say there is a
[connective spectrum](synthetic-homotopy-theory.connective-spectra.md) `𝒜` such
that the ∞-group appears as the first type in the sequence. {{#cite BvDR18}}
I.e., there exists a sequence of increasingly
[connected](foundation.connected-types.md) ∞-groups

```text
  A₀   A₁   A₂   A₃   ⋯   Aᵢ   ⋯
```

such that

```text
  Aᵢ ≃∗ Ω Aᵢ₊₁
```

Abelian ∞-groups thus give an example of another infinitely coherent structure
that is definable in Homotopy Type Theory.

## Definitions

### The connective spectrum condition of being abelian with respect to a universe level

```agda
is-abelian-level-connective-spectrum-condition-∞-Group :
  {l : Level} (l1 : Level) → ∞-Group l → UU (l ⊔ lsuc l1)
is-abelian-level-connective-spectrum-condition-∞-Group l1 G =
  Σ ( Connective-Spectrum l1)
    ( λ A → pointed-type-∞-Group G ≃∗ pointed-type-Connective-Spectrum A 0)
```

### The connective spectrum condition of being abelian

```agda
is-abelian-connective-spectrum-condition-∞-Group :
  {l : Level} → ∞-Group l → UU (lsuc l)
is-abelian-connective-spectrum-condition-∞-Group {l} G =
  is-abelian-level-connective-spectrum-condition-∞-Group l G
```

## References

{{#bibliography}}

## External links

- [abelian infinity-group](https://ncatlab.org/nlab/show/abelian+infinity-group)
  at $n$Lab
