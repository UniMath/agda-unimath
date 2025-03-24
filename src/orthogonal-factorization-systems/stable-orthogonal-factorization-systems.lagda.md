# Stable orthogonal factorization systems

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module orthogonal-factorization-systems.stable-orthogonal-factorization-systems
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import orthogonal-factorization-systems.function-classes funext univalence truncations
open import orthogonal-factorization-systems.orthogonal-factorization-systems funext univalence truncations
```

</details>

## Idea

A **stable orthogonal factorization system**, or **stable factorization system**
for short, is an
[orthogonal factorization system](orthogonal-factorization-systems.orthogonal-factorization-systems.md)
whose left class is stable under [pullbacks](foundation.pullbacks.md). The right
class of an orthogonal factorization system, however, is always stable under
pullbacks.

## Definition

```agda
is-stable-orthogonal-factorization-system :
  {l1 lL lR : Level} →
  orthogonal-factorization-system l1 lL lR → UU (lsuc l1 ⊔ lL)
is-stable-orthogonal-factorization-system OFS =
  is-pullback-stable-function-class
    ( left-class-orthogonal-factorization-system OFS)
```

## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Σ-closed reflective modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)

## References

{{#bibliography}} {{#reference RSS20}}
