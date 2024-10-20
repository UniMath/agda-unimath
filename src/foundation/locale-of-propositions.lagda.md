# The locale of propositions

```agda
module foundation.locale-of-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.large-locale-of-propositions
open import foundation.logical-equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.suplattices
open import order-theory.top-elements-posets
```

</details>

## Idea

The [locale](order-theory.locales.md) of
[propositions](foundation-core.propositions.md) consists of all the propositions
of any [universe level](foundation.universe-levels.md) and is ordered by the
implications between them. [Conjunction](foundation.conjunction.md) gives this
[poset](order-theory.posets.md) the structure of a
[meet-semilattice](order-theory.meet-semilattices.md), and
[existential quantification](foundation.existential-quantification.md) gives it
the structure of a [suplattice](order-theory.suplattices.md).

## Definitions

### The preorder of propositions

```agda
Prop-Preorder : (l : Level) → Preorder (lsuc l) l
Prop-Preorder = preorder-Large-Preorder Prop-Large-Preorder
```

### The poset of propositions

```agda
Prop-Poset : (l : Level) → Poset (lsuc l) l
Prop-Poset = poset-Large-Poset Prop-Large-Poset
```

### Meets in the poset of propositions

```text
has-meets-Prop-Locale :
  has-meets-Poset Prop-Poset
meet-has-meets-Poset has-meets-Prop-Locale = conjunction-Prop
is-greatest-binary-lower-bound-meet-has-meets-Poset
  has-meets-Prop-Locale P Q R =
  is-greatest-binary-lower-bound-conjunction-Prop P Q R
```

### The largest element in the poset of propositions

```agda
has-top-element-Prop-Locale :
  {l : Level} → has-top-element-Poset (Prop-Poset l)
has-top-element-Prop-Locale {l} = (raise-unit-Prop l , λ _ _ → raise-star)
```

### The poset of propositions is a meet-semilattice

```text
is-meet-semilattice-Prop-Locale :
  is-meet-semilattice-Poset Prop-Poset
has-meets-is-meet-semilattice-Poset
  is-meet-semilattice-Prop-Locale =
  has-meets-Prop-Locale
has-top-element-is-meet-semilattice-Poset
  is-meet-semilattice-Prop-Locale =
  has-top-element-Prop-Locale
```

### Suprema in the poset of propositions

```agda
is-suplattice-Prop-Locale :
  (l : Level) → is-suplattice-Poset l (Prop-Poset l)
is-suplattice-Prop-Locale l I P = (∃ I P , inv-iff ∘ up-exists)
```

### The frame of propositions

```text
Prop-Frame : Frame lsuc (_⊔_) lzero
poset-Frame Prop-Frame =
  Prop-Poset
is-meet-semilattice-Frame Prop-Frame =
  is-meet-semilattice-Prop-Locale
is-suplattice-Frame Prop-Frame =
  is-suplattice-Prop-Locale
distributive-meet-sup-Frame Prop-Frame =
  eq-distributive-conjunction-exists
```

### The locale of propositions

```text
Prop-Locale : Locale lsuc (_⊔_) lzero
Prop-Locale = Prop-Frame
```

## See also

- [Propositional resizing](foundation.propositional-resizing.md)
