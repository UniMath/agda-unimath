# Types with decidable universal quantifications

```agda
module foundation.types-with-decidable-universal-quantifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.mere-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.types-with-decidable-dependent-product-types
open import foundation.universe-levels

open import logic.propositionally-decidable-types
```

</details>

## Idea

A type `X`
{{#concept "has decidable universal quantifications" Disambiguation="on type" Agda=has-decidable-∀}}
if, for every [decidable subtype](foundation.decidable-subtypes.md) `P` of `X`,
it is [decidable](foundation.decidable-types.md) if `P` is the
[full subtype](foundation.full-subtypes.md). In other words, we have a witness
of type

```text
  (P : decidable-subtype X) → is-decidable (∀ x. x ∈ P).
```

Note that having decidable universal quantifications is
[logically equivalent](foundation.logical-equivalences.md) to having
[decidable Π-types](foundation.types-with-decidable-dependent-product-types.md),
but the latter is not a [proposition](foundation-core.propositions.md).

**Terminology.** In the terminology of Martín Escardó, a type that has decidable
universal quantifications is referred to as _weakly compact_, or _Π-compact_, or
_satisfying the weak principle of omniscience_. {{#cite TypeTopology}}

## Definitions

### The predicate of having decidable universal quantifications

```agda
has-decidable-∀-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidable-∀-Level l2 X =
  (P : decidable-subtype l2 X) → is-decidable (is-full-decidable-subtype P)

has-decidable-∀ : {l1 : Level} → UU l1 → UUω
has-decidable-∀ X =
  {l2 : Level} → has-decidable-∀-Level l2 X

is-prop-has-decidable-∀-Level :
  {l1 l2 : Level} {X : UU l1} →
  is-prop (has-decidable-∀-Level l2 X)
is-prop-has-decidable-∀-Level =
  is-prop-Π
    ( λ P →
      is-prop-is-decidable
        ( is-prop-is-full-subtype (subtype-decidable-subtype P)))
```

## Properties

### Types with decidable universal quantifications have decidable Π-types

```agda
has-decidable-Π-has-decidable-∀ :
  {l1 : Level} {X : UU l1} →
  has-decidable-∀ X →
  has-decidable-Π X
has-decidable-Π-has-decidable-∀
  f P =
  map-coproduct
    ( λ nnp x →
      rec-coproduct id (ex-falso ∘ nnp x) (is-decidable-decidable-family P x))
    ( λ nnnp p → nnnp (intro-double-negation ∘ p))
    ( f ( λ x →
          neg-type-Decidable-Prop
            ( ¬ (family-decidable-family P x))
            ( is-decidable-neg (is-decidable-decidable-family P x))))
```

### Merely decidable types with merely equal elements have decidable universal quantifications

```agda
abstract
  has-decidable-∀-is-inhabited-or-empty-all-elements-merely-equal :
    {l : Level} {X : UU l} →
    is-inhabited-or-empty X →
    all-elements-merely-equal X →
    has-decidable-∀ X
  has-decidable-∀-is-inhabited-or-empty-all-elements-merely-equal
    { X = X} (inl |x|) H P =
    rec-trunc-Prop
      ( is-decidable-Prop (Π-Prop X (subtype-decidable-subtype P)))
      ( λ x →
        map-coproduct
          ( λ p x' →
            rec-trunc-Prop
              ( subtype-decidable-subtype P x')
              ( λ r → tr (is-in-decidable-subtype P) r p)
              ( H x x'))
          ( map-neg (ev x))
          ( is-decidable-decidable-subtype P x))
      ( |x|)
  has-decidable-∀-is-inhabited-or-empty-all-elements-merely-equal
    ( inr nx) H P =
    inl (ex-falso ∘ nx)

abstract
  has-decidable-Π-is-inhabited-or-empty-all-elements-merely-equal :
    {l : Level} {X : UU l} →
    is-inhabited-or-empty X →
    all-elements-merely-equal X →
    has-decidable-Π X
  has-decidable-Π-is-inhabited-or-empty-all-elements-merely-equal
    d H =
    has-decidable-Π-has-decidable-∀
      ( has-decidable-∀-is-inhabited-or-empty-all-elements-merely-equal
        ( d)
        ( H))

abstract
  has-decidable-Π-is-decidable-all-elements-merely-equal :
    {l : Level} {X : UU l} →
    is-decidable X →
    all-elements-merely-equal X →
    has-decidable-Π X
  has-decidable-Π-is-decidable-all-elements-merely-equal d =
    has-decidable-Π-is-inhabited-or-empty-all-elements-merely-equal
      ( is-inhabited-or-empty-is-decidable d)
```

## References

{{#bibliography}}

## See also

- [Types with decidable Σ-types](foundation.types-with-decidable-dependent-pair-types.md)
- [Types with decidable Π-types](foundation.types-with-decidable-dependent-product-types.md)
