# π-finite types

```agda
module univalent-combinatorics.pi-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.set-truncations
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.untruncated-pi-finite-types
```

</details>

## Idea

A type is
{{#concept "πₙ-finite" Disambiguation="type" Agda=is-truncated-π-finite Agda=Truncated-π-Finite}}
if it has [finitely](univalent-combinatorics.finite-types.md) many
[connected components](foundation.connected-components.md), all of its homotopy
groups up to level `n` at all base points are finite, and all higher homotopy
groups are [trivial](group-theory.trivial-groups.md). A type is
{{#concept "π-finite"}} if it is πₙ-finite for some `n`.

## Definitions

### π-finite types

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

### πₙ-finite types are n-truncated

```agda
is-trunc-is-truncated-π-finite :
  {l : Level} (k : ℕ) {X : UU l} →
  is-truncated-π-finite k X → is-trunc (truncation-level-ℕ k) X
is-trunc-is-truncated-π-finite zero-ℕ = is-set-is-finite
is-trunc-is-truncated-π-finite (succ-ℕ k) H x y =
  is-trunc-is-truncated-π-finite k (pr2 H x y)
```

### Untruncated πₙ-finite n-truncated types are πₙ-finite

```agda
is-truncated-π-finite-is-untruncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-trunc (truncation-level-ℕ k) A →
  is-untruncated-π-finite k A → is-truncated-π-finite k A
is-truncated-π-finite-is-untruncated-π-finite zero-ℕ H K =
  is-finite-is-untruncated-π-finite zero-ℕ H K
pr1 (is-truncated-π-finite-is-untruncated-π-finite (succ-ℕ k) H K) = pr1 K
pr2 (is-truncated-π-finite-is-untruncated-π-finite (succ-ℕ k) H K) x y =
  is-truncated-π-finite-is-untruncated-π-finite k (H x y) (pr2 K x y)
```

### πₙ-finite types are untruncated πₙ-finite

```agda
is-untruncated-π-finite-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-truncated-π-finite k A → is-untruncated-π-finite k A
is-untruncated-π-finite-is-truncated-π-finite zero-ℕ H =
  is-finite-equiv
    ( equiv-unit-trunc-Set (_ , (is-set-is-finite H)))
    ( H)
pr1 (is-untruncated-π-finite-is-truncated-π-finite (succ-ℕ k) H) = pr1 H
pr2 (is-untruncated-π-finite-is-truncated-π-finite (succ-ℕ k) H) x y =
  is-untruncated-π-finite-is-truncated-π-finite k (pr2 H x y)
```

## See also

- [Unbounded π-finite types](univalent-combinatorics.unbounded-pi-finite-types.md)

## External links

- [pi-finite type](https://ncatlab.org/nlab/show/pi-finite+type) at $n$Lab
