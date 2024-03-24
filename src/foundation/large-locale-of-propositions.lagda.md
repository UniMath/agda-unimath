# The large locale of propositions

```agda
module foundation.large-locale-of-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions

open import order-theory.large-frames
open import order-theory.large-locales
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.top-elements-large-posets
```

</details>

## Idea

The [large locale](order-theory.large-locales.md) of
[propositions](foundation-core.propositions.md) consists of all the propositions
of any [universe level](foundation.universe-levels.md) and is ordered by the
[implications](foundation.implication.md) between them.
[Conjunction](foundation.conjunction.md) gives this
[large poset](order-theory.large-posets.md) the structure of a
[large meet-semilattice](order-theory.large-meet-semilattices.md), and
[existential quantification](foundation.existential-quantification.md) gives it
the structure of a [large suplattice](forder-theory.large-suplattices.md).

**Note.** The collection of all propositions is large because we do not assume
[propositional resizing](foundation.propositional-resizing.md).

## Definitions

### The large preorder of propositions

```agda
Prop-Large-Preorder : Large-Preorder lsuc (_⊔_)
type-Large-Preorder Prop-Large-Preorder = Prop
leq-prop-Large-Preorder Prop-Large-Preorder = hom-Prop
refl-leq-Large-Preorder Prop-Large-Preorder P = id
transitive-leq-Large-Preorder Prop-Large-Preorder P Q R g f = g ∘ f
```

### The large poset of propositions

```agda
Prop-Large-Poset : Large-Poset lsuc (_⊔_)
large-preorder-Large-Poset Prop-Large-Poset = Prop-Large-Preorder
antisymmetric-leq-Large-Poset Prop-Large-Poset P Q = eq-iff
```

### Meets in the large poset of propositions

```agda
has-meets-Prop-Large-Locale :
  has-meets-Large-Poset Prop-Large-Poset
meet-has-meets-Large-Poset has-meets-Prop-Large-Locale = conjunction-Prop
is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
  has-meets-Prop-Large-Locale P Q R =
  is-greatest-binary-lower-bound-conjunction-Prop P Q R
```

### The largest element in the large poset of propositions

```agda
has-top-element-Prop-Large-Locale :
  has-top-element-Large-Poset Prop-Large-Poset
top-has-top-element-Large-Poset
  has-top-element-Prop-Large-Locale = unit-Prop
is-top-element-top-has-top-element-Large-Poset
  has-top-element-Prop-Large-Locale P p =
  star
```

### The large poset of propositions is a large meet-semilattice

```agda
is-large-meet-semilattice-Prop-Large-Locale :
  is-large-meet-semilattice-Large-Poset Prop-Large-Poset
has-meets-is-large-meet-semilattice-Large-Poset
  is-large-meet-semilattice-Prop-Large-Locale =
  has-meets-Prop-Large-Locale
has-top-element-is-large-meet-semilattice-Large-Poset
  is-large-meet-semilattice-Prop-Large-Locale =
  has-top-element-Prop-Large-Locale
```

### Suprema in the large poset of propositions

```agda
is-large-suplattice-Prop-Large-Locale :
  is-large-suplattice-Large-Poset lzero Prop-Large-Poset
sup-has-least-upper-bound-family-of-elements-Large-Poset
  ( is-large-suplattice-Prop-Large-Locale {I = I} P) =
  ∃ I P
is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset
  ( is-large-suplattice-Prop-Large-Locale {I = I} P) R =
  inv-iff (up-exists R)
```

### The large frame of propositions

```agda
Prop-Large-Frame : Large-Frame lsuc (_⊔_) lzero
large-poset-Large-Frame Prop-Large-Frame =
  Prop-Large-Poset
is-large-meet-semilattice-Large-Frame Prop-Large-Frame =
  is-large-meet-semilattice-Prop-Large-Locale
is-large-suplattice-Large-Frame Prop-Large-Frame =
  is-large-suplattice-Prop-Large-Locale
distributive-meet-sup-Large-Frame Prop-Large-Frame =
  eq-distributive-conjunction-exists
```

### The large locale of propositions

```agda
Prop-Large-Locale : Large-Locale lsuc (_⊔_) lzero
Prop-Large-Locale = Prop-Large-Frame
```

## See also

- [Propositional resizing](foundation.propositional-resizing.md)
