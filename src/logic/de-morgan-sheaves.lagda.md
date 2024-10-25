# De Morgan sheaves

```agda
module logic.de-morgan-sheaves where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import logic.de-morgans-law
open import foundation.coproduct-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.irrefutable-propositions
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions

open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

{{#concept "De morgan sheaves" Agda=is-de-morgan-sheaf}} are types that are
[null](orthogonal-factorization-systems.null-types.md) at propositions of the
form `¬ P ∨ ¬¬ P`.

De Morgan sheaves are closely related to, but a strictly weaker notion than that
of
[double negation sheaves](orthogonal-factorization-systems.double-negation-sheaves.md).

## Definitions

### The property of being a De Morgan sheaf

```agda
is-de-morgan-sheaf :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
is-de-morgan-sheaf l1 A =
  (P : Prop l1) → is-null (is-decidable (¬ P)) A

is-prop-is-de-morgan-sheaf :
  {l1 l2 : Level} {A : UU l2} → is-prop (is-de-morgan-sheaf l1 A)
is-prop-is-de-morgan-sheaf {A = A} =
  is-prop-Π (λ P → is-prop-is-null (type-Irrefutable-Prop P) A)
```

## Properties

### A type is a De Morgan sheaf if and only if it is local at the De Morgan implication

A type null at `¬P ∨ ¬¬ P` for all propositions `P` if and only if it is local
at `(¬ P ∨ ¬ Q) ⇒ ¬ (P ∧ Q)` for all propositions `P` and `Q`.

### The empty type is a De Morgan sheaf

```agda
is-de-morgan-sheaf-empty :
  {l : Level} → is-de-morgan-sheaf l empty
is-de-morgan-sheaf-empty P =
  is-equiv-has-converse empty-Prop
    ( hom-Prop (prop-Irrefutable-Prop P) empty-Prop)
    ( is-irrefutable-Irrefutable-Prop P)
```

### Contractible types are De Morgan sheaves

```agda
is-de-morgan-sheaf-is-contr :
  {l1 l2 : Level} {A : UU l1} → is-contr A → is-de-morgan-sheaf l2 A
is-de-morgan-sheaf-is-contr is-contr-A P =
  is-null-is-contr (type-Irrefutable-Prop P) is-contr-A
```

### Propositions that are De Morgan sheaves are De Morgan

```agda
module _
  {l : Level} {A : UU l}
  (is-prop-A : is-prop A)
  (is-¬¬sheaf-A : is-de-morgan-sheaf l A)
  where

  -- compute-is-de-morgan-sheaf-is-prop : A ≃ (¬ A → A)
  -- compute-is-de-morgan-sheaf-is-prop =
  --   ( left-unit-law-product-is-contr
  --     ( is-proof-irrelevant-is-prop (is-prop-function-type is-prop-A) id)) ∘e
  --   ( equiv-universal-property-coproduct A) ∘e
  --   ( _ , is-¬¬sheaf-A (is-decidable-prop-Irrefutable-Prop (A , is-prop-A)))

  -- is-de-morgan-stable-is-de-morgan-sheaf-is-prop :
  --   is-de-morgan-stable (A , is-prop-A)
  -- is-de-morgan-stable-is-de-morgan-sheaf-is-prop ¬¬a =
  --   map-inv-is-equiv (is-¬¬sheaf-A (A , is-prop-A , ¬¬a)) id
```

### Double negation stable propositions are De Morgan sheaves

This follows from the fact that a proposition `P` is double negation stable if
and only if it is local at all double negations

```text
  (¬¬A → P) → (A → P),
```

and nullification at irrefutable propositions is a restriction of this.

> This remains to be formalized.

### The negation of a type is a De Morgan sheaf

This is a corollary of the previous result.

> This remains to be formalized.

## References

{{#bibliography}}
