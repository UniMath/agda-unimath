# The locale of propositions

```agda
module foundation.locale-of-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.large-locale-of-propositions
open import foundation.logical-equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types

open import order-theory.frames
open import order-theory.greatest-lower-bounds-posets
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.meet-semilattices
open import order-theory.meet-suplattices
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

### The largest element in the poset of propositions

```agda
has-top-element-Prop-Locale :
  {l : Level} → has-top-element-Poset (Prop-Poset l)
has-top-element-Prop-Locale {l} = (raise-unit-Prop l , λ _ _ → raise-star)
```

### Meets in the poset of propositions

```agda
is-meet-semilattice-Prop-Locale :
  {l : Level} → is-meet-semilattice-Poset (Prop-Poset l)
is-meet-semilattice-Prop-Locale P Q =
  ( P ∧ Q , is-greatest-binary-lower-bound-conjunction-Prop P Q)

Prop-Order-Theoretic-Meet-Semilattice :
  (l : Level) → Order-Theoretic-Meet-Semilattice (lsuc l) l
Prop-Order-Theoretic-Meet-Semilattice l =
  Prop-Poset l , is-meet-semilattice-Prop-Locale

Prop-Meet-Semilattice :
  (l : Level) → Meet-Semilattice (lsuc l)
Prop-Meet-Semilattice l =
  meet-semilattice-Order-Theoretic-Meet-Semilattice
    ( Prop-Order-Theoretic-Meet-Semilattice l)
```

### Suprema in the poset of propositions

```agda
is-suplattice-lzero-Prop-Locale :
  {l : Level} → is-suplattice-Poset lzero (Prop-Poset l)
is-suplattice-lzero-Prop-Locale I P = (∃ I P , inv-iff ∘ up-exists)

is-suplattice-Prop-Locale :
  {l : Level} → is-suplattice-Poset l (Prop-Poset l)
is-suplattice-Prop-Locale I P = (∃ I P , inv-iff ∘ up-exists)

Prop-Suplattice :
  (l : Level) → Suplattice (lsuc l) l l
Prop-Suplattice l = Prop-Poset l , is-suplattice-Prop-Locale
```

```text
is-meet-suplattice-Prop-Locale :
  {l : Level} → is-meet-suplattice-Meet-Semilattice l (Prop-Meet-Semilattice l)
is-meet-suplattice-Prop-Locale I P = ？

Prop-Meet-Suplattice :
  (l : Level) → Meet-Suplattice (lsuc l) l
Prop-Meet-Suplattice l =
  Prop-Meet-Semilattice l , is-meet-suplattice-Prop-Locale
```

### The frame of propositions

```text
Prop-Frame : (l : Level) → Frame (lsuc l) l
Prop-Frame l = Prop-Meet-Suplattice l , ？
```

### The locale of propositions

```text
Prop-Locale : Locale lsuc (_⊔_) lzero
Prop-Locale = Prop-Frame
```

## See also

- [Propositional resizing](foundation.propositional-resizing.md)
