# Double negation

```agda
module foundation.double-negation where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.functions
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Definition

We define double negation and triple negation

```agda
¬¬ : {l : Level} → UU l → UU l
¬¬ P = ¬ (¬ P)

¬¬¬ : {l : Level} → UU l → UU l
¬¬¬ P = ¬ (¬ (¬ P))
```

We also define the introduction rule for double negation, and the action on maps of double negation.

```agda
intro-dn : {l : Level} {P : UU l} → P → ¬¬ P
intro-dn p f = f p

map-dn : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬¬ P → ¬¬ Q)
map-dn f = map-neg (map-neg f)
```

## Properties

### The double negation of a type is a proposition

```agda
dn-Prop' :
  {l : Level} (A : UU l) → Prop l
dn-Prop' A = neg-Prop' (¬ A)

dn-Prop :
  {l : Level} (P : Prop l) → Prop l
dn-Prop P = dn-Prop' (type-Prop P)
```

### Double negations of classical laws

```agda
dn-dn-elim : {l : Level} {P : UU l} → ¬¬ (¬¬ P → P)
dn-dn-elim {P = P} f =
  ( λ (np : ¬ P) → f (λ (nnp : ¬¬ P) → ex-falso (nnp np)))
    ( λ (p : P) → f (λ (nnp : ¬¬ P) → p))

dn-Peirces-law :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (((P → Q) → P) → P)
dn-Peirces-law {P = P} {Q} f =
  ( λ (np : ¬ P) → f (λ h → h (λ p → ex-falso (np p))))
  ( λ (p : P) → f (λ h → p))

dn-linearity-implication :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ ((P → Q) + (Q → P))
dn-linearity-implication {P = P} {Q = Q} f =
  ( λ (np : ¬ P) →
    map-neg (inl {A = P → Q} {B = Q → P}) f (λ p → ex-falso (np p)))
    ( λ (p : P) →
      map-neg (inr {A = P → Q} {B = Q → P}) f (λ q → p))
```

### Cases of double negation elimination

```agda
dn-elim-neg : {l : Level} (P : UU l) → ¬¬¬ P → ¬ P
dn-elim-neg P f p = f (λ g → g p)

dn-elim-prod :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ ((¬¬ P) × (¬¬ Q)) → (¬¬ P) × (¬¬ Q)
pr1 (dn-elim-prod {P = P} {Q = Q} f) = dn-elim-neg (¬ P) (map-dn pr1 f)
pr2 (dn-elim-prod {P = P} {Q = Q} f) = dn-elim-neg (¬ Q) (map-dn pr2 f)

dn-elim-exp :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (P → ¬¬ Q) → (P → ¬¬ Q)
dn-elim-exp {P = P} {Q = Q} f p =
  dn-elim-neg (¬ Q) (map-dn (λ (g : P → ¬¬ Q) → g p) f)

dn-elim-forall :
  {l1 l2 : Level} {P : UU l1} {Q : P → UU l2} →
  ¬¬ ((p : P) → ¬¬ (Q p)) → (p : P) → ¬¬ (Q p)
dn-elim-forall {P = P} {Q = Q} f p =
  dn-elim-neg (¬ (Q p)) (map-dn (λ (g : (u : P) → ¬¬ (Q u)) → g p) f)
```

### Maps into double negations extend along `intro-dn`

```agda
dn-extend :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
dn-extend {P = P} {Q = Q} f = dn-elim-neg (¬ Q) ∘ (map-dn f)
```

### A double negation of a type is logially equivalent to the double negation of its propositional truncation

```agda
abstract
  dn-dn-type-trunc-Prop :
    {l : Level} (A : UU l) → ¬¬ (type-trunc-Prop A) → ¬¬ A
  dn-dn-type-trunc-Prop A =
    dn-extend (map-universal-property-trunc-Prop (dn-Prop' A) intro-dn)

abstract
  dn-type-trunc-Prop-dn :
    {l : Level} {A : UU l} → ¬¬ A → ¬¬ (type-trunc-Prop A)
  dn-type-trunc-Prop-dn = map-dn unit-trunc-Prop
```
