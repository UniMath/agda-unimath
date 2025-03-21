# Logical equivalences

```agda
module foundation.logical-equivalences where

open import foundation-core.logical-equivalences public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

{{#concept "Logical equivalences" Disambiguation="of types" Agda=iff}} between
two types `A` and `B` consist of a map `A → B` and a map `B → A`. The type of
logical equivalences between types is the
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of logical equivalences between [propositions](foundation-core.propositions.md).

## Definition

### The structure on a map of being a logical equivalence

```agda
is-prop-has-converse :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-prop A → (f : A → B) → is-prop (has-converse f)
is-prop-has-converse is-prop-A f = is-prop-function-type is-prop-A

has-converse-Prop :
  {l1 l2 : Level} (A : Prop l1) {B : UU l2} → (type-Prop A → B) → Prop (l1 ⊔ l2)
has-converse-Prop A f =
  ( has-converse f ,
    is-prop-has-converse (is-prop-type-Prop A) f)
```

### Logical equivalences between propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  type-iff-Prop : UU (l1 ⊔ l2)
  type-iff-Prop = type-Prop P ↔ type-Prop Q

  is-prop-iff-Prop : is-prop type-iff-Prop
  is-prop-iff-Prop =
    is-prop-product
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( is-prop-function-type (is-prop-type-Prop P))

  iff-Prop : Prop (l1 ⊔ l2)
  pr1 iff-Prop = type-iff-Prop
  pr2 iff-Prop = is-prop-iff-Prop

  infix 6 _⇔_

  _⇔_ : Prop (l1 ⊔ l2)
  _⇔_ = iff-Prop
```

## Properties

### Characterizing equality of logical equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  ext-iff : (f g : A ↔ B) → (f ＝ g) ≃ htpy-iff f g
  ext-iff f g = equiv-product equiv-funext equiv-funext ∘e equiv-pair-eq f g

  refl-htpy-iff : (f : A ↔ B) → htpy-iff f f
  pr1 (refl-htpy-iff f) = refl-htpy
  pr2 (refl-htpy-iff f) = refl-htpy

  htpy-eq-iff : {f g : A ↔ B} → f ＝ g → htpy-iff f g
  htpy-eq-iff {f} {g} = map-equiv (ext-iff f g)

  eq-htpy-iff : (f g : A ↔ B) → htpy-iff f g → (f ＝ g)
  eq-htpy-iff f g = map-inv-equiv (ext-iff f g)
```

### Logical equivalence of propositions is equivalent to equivalence of propositions

```agda
abstract
  is-equiv-equiv-iff :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-equiv (equiv-iff' P Q)
  is-equiv-equiv-iff P Q =
    is-equiv-has-converse-is-prop
      ( is-prop-iff-Prop P Q)
      ( is-prop-type-equiv-Prop P Q)
      ( iff-equiv)

equiv-equiv-iff :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  (type-Prop P ↔ type-Prop Q) ≃ (type-Prop P ≃ type-Prop Q)
pr1 (equiv-equiv-iff P Q) = equiv-iff' P Q
pr2 (equiv-equiv-iff P Q) = is-equiv-equiv-iff P Q
```

### Equivalences are logical equivalences

```agda
compute-fiber-iff-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} ((f , g) : A ↔ B) →
  fiber (iff-equiv) (f , g) ≃ Σ (is-equiv f) (λ f' → map-inv-is-equiv f' ~ g)
compute-fiber-iff-equiv {A = A} {B} e =
  equiv-tot (λ _ → equiv-funext) ∘e compute-fiber-iff-equiv' e
```
