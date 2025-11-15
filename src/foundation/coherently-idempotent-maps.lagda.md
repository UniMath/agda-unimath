# Coherently idempotent maps

```agda
module foundation.coherently-idempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.homotopy-algebra
open import foundation.quasicoherently-idempotent-maps
open import foundation.split-idempotent-maps
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sets
```

</details>

## Idea

A
{{#concept "coherently idempotent map" Disambiguation="of types" Agda=is-coherently-idempotent}}
is an [idempotent](foundation.idempotent-maps.md) map `f : A → A`
[equipped](foundation.structure.md) with an infinitely coherent hierarchy of
[homotopies](foundation-core.homotopies.md) making it a "homotopy-correct"
definition of an idempotent map in Homotopy Type Theory.

The infinite coherence condition is given by taking the
[sequential limit](foundation.sequential-limits.md) of iterated application of
the splitting construction on
[quasicoherently idempotent maps](foundation.quasicoherently-idempotent-maps.md)
given in {{#cite Shu17}}:

```text
  is-coherently-idempotent f :=
    Σ (a : ℕ → is-quasicoherently-idempotent f), (Π (n : ℕ), split(aₙ₊₁) ~ aₙ)
```

**Terminology.** Our definition of a _coherently idempotent map_ corresponds to
the definition of a _(fully coherent) idempotent map_ in {{#cite Shu17}} and
{{#cite Shu14SplittingIdempotents}}. Our definition of an _idempotent map_
corresponds in their terminology to a _pre-idempotent map_.

## Definitions

### The structure on a map of coherent idempotence

```agda
is-coherently-idempotent : {l : Level} {A : UU l} → (A → A) → UU l
is-coherently-idempotent f =
  Σ ( ℕ → is-quasicoherently-idempotent f)
    ( λ a →
      (n : ℕ) →
      htpy-is-quasicoherently-idempotent
        ( is-quasicoherently-idempotent-is-split-idempotent
          ( is-split-idempotent-is-quasicoherently-idempotent
            ( a (succ-ℕ n))))
        ( a n))
```

## See also

- [Split idempotent maps](foundation.split-idempotent-maps.md)

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
