# The continuation modalities

```agda
module orthogonal-factorization-systems.continuation-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.evaluation-functions
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.transport-along-identifications

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

Given a [proposition](foundation-core.propositions.md) `R`, the continuation
monad

```text
  A ↦ ((A → R) → R)
```

defines a
[higher modality](orthogonal-factorization-systems.higher-modalities.md).

## Definitions

### The underlying operators of the continuation modalities

```agda
module _
  {l1 : Level} (l : Level) (R : UU l1)
  where

  operator-continuation-modality : operator-modality l (l1 ⊔ l)
  operator-continuation-modality X = ((X → R) → R)

  unit-continuation-modality :
    unit-modality operator-continuation-modality
  unit-continuation-modality = ev

continuation-extend :
  {l1 l2 l3 : Level} {R : UU l1} {A : UU l2} {B : UU l3} →
  (A → ((B → R) → R)) →
  (((A → R) → R) → ((B → R) → R))
continuation-extend f c g = c (λ a → f a g)
```

## Properties

### Continuations into propositions form uniquely eliminating modalities

```agda
is-uniquely-eliminating-modality-continuation-modality :
  {l1 : Level} (l : Level) (R : Prop l1) →
  is-uniquely-eliminating-modality (unit-continuation-modality l (type-Prop R))
is-uniquely-eliminating-modality-continuation-modality l R P =
  is-local-dependent-type-is-prop
    ( unit-continuation-modality l (type-Prop R))
    ( operator-continuation-modality l (type-Prop R) ∘ P)
    ( λ _ → is-prop-function-type (is-prop-type-Prop R))
    ( λ f z →
      continuation-extend
        ( λ a →
          tr
            ( operator-continuation-modality l (type-Prop R) ∘ P)
            ( eq-is-prop (is-prop-function-type (is-prop-type-Prop R)))
            ( f a))
        ( z))
```

This proof is a generalization of Example 1.9 in {{#cite RSS20}}, where the
special case when `R` is the [empty type](foundation-core.empty-types.md) is
considered.

## References

{{#bibliography}}

## External links

- [continuation monad](https://ncatlab.org/nlab/show/continuation+monad) at
  $n$Lab
