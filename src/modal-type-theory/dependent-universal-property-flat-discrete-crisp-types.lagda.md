# Dependent universal property of flat discrete crisp types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.dependent-universal-property-flat-discrete-crisp-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.universe-levels

open import modal-type-theory.flat-modality
```

</details>

## Idea

The
{{#concept "dependent universal property" Disambiguation="of flat discrete crisp types"}}
of a [flat discrete crisp type](modal-type-theory.flat-discrete-crisp-types.md)
`A` states that for any [crisp](modal-type-theory.crisp-types.md) type family
[defined on crisp elements](modal-type-theory.crisp-function-types.md)
`@♭ B : @♭ A → 𝒰`,
[postcomposition](foundation-core.postcomposition-functions.md) by the counit of
the [flat modality](modal-type-theory.flat-modality.md) induces an
[equivalence](foundation-core.equivalences.md) under the flat modality.

## Definitions

### The dependent universal property of flat discrete crisp types

```agda
dependent-coev-flat :
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2} →
  ♭ ((@♭ x : A) → ♭ (B x)) → ♭ ((@♭ x : A) → B x)
dependent-coev-flat (intro-flat f) = intro-flat (λ x → counit-flat (f x))
```

```text
dependent-universal-property-flat-discrete-crisp-type :
  {@♭ l1 : Level} (@♭ A : UU l1) → UUω
dependent-universal-property-flat-discrete-crisp-type A =
  {@♭ l : Level} {@♭ B : @♭ A → UU l} → is-equiv (dependent-coev-flat {B = B})
```

## Properties

### Flat discrete crisp types satisfy the dependent universal property of flat discrete crisp types

This remains to be formalized.

## See also

- [The universal property of flat discrete crisp types](modal-type-theory.universal-property-flat-discrete-crisp-types.md)

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
