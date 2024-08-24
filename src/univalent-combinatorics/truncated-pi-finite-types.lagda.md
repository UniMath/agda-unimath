# Truncated π-finite types

```agda
module univalent-combinatorics.truncated-pi-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-set-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.maybe
open import foundation.mere-equality
open import foundation.mere-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-presented-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.finitely-presented-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type is
{{#concept "truncated πₙ-finite" Disambiguation="type" Agda=is-truncated-π-finite Agda=Truncated-π-Finite}}
if it has [finitely](univalent-combinatorics.finite-types.md) many
[connected components](foundation.connected-components.md), all of its homotopy
groups up to level `n` at all base points are finite, and all higher homotopy
groups are [contractible](foundation-core.contractible-types.md).

## Definitions

### Truncated π-finite types

```agda
is-truncated-π-finite-Prop : {l : Level} (k : ℕ) → UU l → Prop l
is-truncated-π-finite-Prop zero-ℕ X = is-finite-Prop X
is-truncated-π-finite-Prop (succ-ℕ k) X =
  product-Prop
    ( has-finitely-many-connected-components-Prop X)
    ( Π-Prop X
      ( λ x → Π-Prop X (λ y → is-truncated-π-finite-Prop k (x ＝ y))))

is-truncated-π-finite : {l : Level} (k : ℕ) → UU l → UU l
is-truncated-π-finite k A =
  type-Prop (is-truncated-π-finite-Prop k A)

is-prop-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-prop (is-truncated-π-finite k A)
is-prop-is-truncated-π-finite k {A} =
  is-prop-type-Prop (is-truncated-π-finite-Prop k A)

has-finitely-many-connected-components-is-truncated-π-finite :
  {l : Level} (k : ℕ) {X : UU l} →
  is-truncated-π-finite k X → has-finitely-many-connected-components X
has-finitely-many-connected-components-is-truncated-π-finite zero-ℕ =
  has-finitely-many-connected-components-is-finite
has-finitely-many-connected-components-is-truncated-π-finite (succ-ℕ k) = pr1
```

## Properties

### Truncated πₙ-finite types are n-truncated

```agda
is-trunc-is-truncated-π-finite :
  {l : Level} (k : ℕ) {X : UU l} →
  is-truncated-π-finite k X → is-trunc (truncation-level-ℕ k) X
is-trunc-is-truncated-π-finite zero-ℕ = is-set-is-finite
is-trunc-is-truncated-π-finite (succ-ℕ k) H x y =
  is-trunc-is-truncated-π-finite k (pr2 H x y)
```

### πₙ-finite n-truncated types are truncated πₙ-finite

```agda
is-truncated-π-finite-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-trunc (truncation-level-ℕ k) A →
  is-π-finite k A → is-truncated-π-finite k A
is-truncated-π-finite-is-π-finite zero-ℕ H K =
  is-finite-is-π-finite zero-ℕ H K
pr1 (is-truncated-π-finite-is-π-finite (succ-ℕ k) H K) = pr1 K
pr2 (is-truncated-π-finite-is-π-finite (succ-ℕ k) H K) x y =
  is-truncated-π-finite-is-π-finite k (H x y) (pr2 K x y)
```

### Truncated πₙ-finite types are πₙ-finite

```agda
is-π-finite-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-truncated-π-finite k A → is-π-finite k A
is-π-finite-is-truncated-π-finite zero-ℕ H =
  is-finite-equiv
    ( equiv-unit-trunc-Set (_ , (is-set-is-finite H)))
    ( H)
pr1 (is-π-finite-is-truncated-π-finite (succ-ℕ k) H) = pr1 H
pr2 (is-π-finite-is-truncated-π-finite (succ-ℕ k) H) x y =
  is-π-finite-is-truncated-π-finite k (pr2 H x y)
```

## See also

- [Unbounded π-finite types](univalent-combinatorics.unbounded-pi-finite-types.md)
