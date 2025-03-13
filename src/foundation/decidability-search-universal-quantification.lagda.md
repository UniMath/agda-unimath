# ∀-Decidability search

```agda
module foundation.decidability-search-universal-quantification where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.decidability-search-untruncated-existential-quantification
open import foundation.decidability-search-untruncated-universal-quantification
open import foundation.decidable-dependent-function-types
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.fibers-of-maps
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.irrefutable-equality
open import foundation.locally-small-types
open import foundation.mere-equality
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.small-types
open import foundation.surjective-maps
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types

open import logic.complements-decidable-subtypes
open import logic.de-morgan-subtypes
open import logic.de-morgan-types
open import logic.double-negation-dense-maps
open import logic.propositionally-decidable-types

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type `X` has
{{#concept "∀-decidability search" Disambiguation="on type" Agda=has-∀-decidability-search}},
or is **∀-decidability searchable**, if we have a terminating algorithm `f`
that, for every [decidable subtype](foundation.decidable-subtypes.md) `P` of `X`
decides if `P` is the full subtype. In other words, `f` is an element of type

```text
  (P : decidable-subtype X) → is-decidable (∀ x. x ∈ P).
```

Having ∀-decidability search is
[logically equivalent](foundation.logical-equivalences.md) to having
Π-decidability search, but the latter is not a
[proposition](foundation-core.propositions.md).

**Terminology.** In the terminology of Martín Escardó, a type that has
∀-decidability search is referred to as _weakly compact_, or _Π-compact_, or
_satisfying the weak principle of omniscience_. {{#cite TypeTopology}}

## Definitions

### The predicate of having ∀-decidability search

```agda
has-∀-decidability-search-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-∀-decidability-search-Level l2 X =
  (P : decidable-subtype l2 X) → is-decidable (is-full-decidable-subtype P)

has-∀-decidability-search : {l1 : Level} → UU l1 → UUω
has-∀-decidability-search X =
  {l2 : Level} → has-∀-decidability-search-Level l2 X

is-prop-has-∀-decidability-search-Level :
  {l1 l2 : Level} {X : UU l1} →
  is-prop (has-∀-decidability-search-Level l2 X)
is-prop-has-∀-decidability-search-Level =
  is-prop-Π
    ( λ P →
      is-prop-is-decidable
        ( is-prop-is-full-subtype (subtype-decidable-subtype P)))
```

## Properties

### Types with ∀-decidability search have Π-decidability search

```agda
has-Π-decidability-search-has-∀-decidability-search :
  {l1 : Level} {X : UU l1} →
  has-∀-decidability-search X →
  has-Π-decidability-search X
has-Π-decidability-search-has-∀-decidability-search
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

### Merely decidable types with merely equal elements have ∀-decidability search

```agda
abstract
  has-∀-decidability-search-is-inhabited-or-empty-all-elements-merely-equal :
    {l : Level} {X : UU l} →
    is-inhabited-or-empty X →
    all-elements-merely-equal X →
    has-∀-decidability-search X
  has-∀-decidability-search-is-inhabited-or-empty-all-elements-merely-equal
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
  has-∀-decidability-search-is-inhabited-or-empty-all-elements-merely-equal
    ( inr nx) H P =
    inl (ex-falso ∘ nx)

abstract
  has-Π-decidability-search-is-inhabited-or-empty-all-elements-merely-equal :
    {l : Level} {X : UU l} →
    is-inhabited-or-empty X →
    all-elements-merely-equal X →
    has-Π-decidability-search X
  has-Π-decidability-search-is-inhabited-or-empty-all-elements-merely-equal
    d H =
    has-Π-decidability-search-has-∀-decidability-search
      ( has-∀-decidability-search-is-inhabited-or-empty-all-elements-merely-equal
        ( d)
        ( H))

abstract
  has-Π-decidability-search-is-decidable-all-elements-merely-equal :
    {l : Level} {X : UU l} →
    is-decidable X →
    all-elements-merely-equal X →
    has-Π-decidability-search X
  has-Π-decidability-search-is-decidable-all-elements-merely-equal d =
    has-Π-decidability-search-is-inhabited-or-empty-all-elements-merely-equal
      ( is-inhabited-or-empty-is-decidable d)
```

## References

{{#bibliography}}

## See also

- [Σ-decidability search](foundation.decidability-search-untruncated-existential-quantification.md)
- [Π-decidability search](foundation.decidability-search-untruncated-universal-quantification.md)
