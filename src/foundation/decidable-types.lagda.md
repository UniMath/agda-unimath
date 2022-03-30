# Decidable types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.decidable-types where

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using
  ( coprod; inl; inr; ind-coprod; is-prop-coprod; is-left; is-right)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.double-negation using (¬¬; intro-dn)
open import foundation.empty-types using
  ( empty; ex-falso; is-empty; empty-Prop; is-nonempty-is-inhabited)
open import foundation.equivalences using
  ( is-equiv; _≃_; map-inv-equiv; map-equiv; inv-equiv)
open import foundation.functions using (id; _∘_)
open import foundation.hilberts-epsilon-operators using (ε-operator-Hilbert)
open import foundation.negation using (¬; map-neg; is-prop-neg)
open import foundation.retractions using (_retract-of_)
open import foundation.propositions using
  ( is-prop; UU-Prop; type-Prop; is-prop-type-Prop)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; apply-universal-property-trunc-Prop;
    is-prop-type-trunc-Prop; trunc-Prop; unit-trunc-Prop;
    map-universal-property-trunc-Prop)
open import foundation.raising-universe-levels using (raise; map-inv-raise; map-raise)
open import foundation.type-arithmetic-empty-type using
  ( right-unit-law-coprod-is-empty)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

A type is said to be decidable if we can either construct an element, or we can prove that it is empty. In other words, we interpret decidability via the Curry-Howard interpretation of logic into type theory. A related concept is that a type is either inhabited or empty, where inhabitedness of a type is expressed using the propositional truncation.

## Definition

### The Curry-Howard interpretation of decidability

```agda
is-decidable : {l : Level} (A : UU l) → UU l
is-decidable A = coprod A (¬ A)

is-decidable-fam :
  {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-fam {A = A} P = (x : A) → is-decidable (P x)
```

### The predicate that a type is inhabited or empty

```agda
is-inhabited-or-empty : {l1 : Level} → UU l1 → UU l1
is-inhabited-or-empty A = coprod (type-trunc-Prop A) (is-empty A)
```

### A type `A` is said to be merely decidable if it comes equipped with an element of `type-trunc-Prop (is-decidable A)`.

```agda
is-merely-decidable-Prop :
  {l : Level} → UU l → UU-Prop l
is-merely-decidable-Prop A = trunc-Prop (is-decidable A)

is-merely-decidable : {l : Level} → UU l → UU l
is-merely-decidable A = type-trunc-Prop (is-decidable A)
```

## Examples


### The unit type and the empty type are decidable

```
is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id
```

### Being on the left or on the right in a coproduct is decidable

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where
  
  is-decidable-is-left : (x : coprod X Y) → is-decidable (is-left x)
  is-decidable-is-left (inl x) = is-decidable-unit
  is-decidable-is-left (inr x) = is-decidable-empty

  is-decidable-is-right : (x : coprod X Y) → is-decidable (is-right x)
  is-decidable-is-right (inl x) = is-decidable-empty
  is-decidable-is-right (inr x) = is-decidable-unit
```

## Properties

### Coproducts of decidable types are decidable

```agda
is-decidable-coprod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (coprod A B)
is-decidable-coprod (inl a) y = inl (inl a)
is-decidable-coprod (inr na) (inl b) = inl (inr b)
is-decidable-coprod (inr na) (inr nb) = inr (ind-coprod (λ x → empty) na nb)
```

### Cartesian products of decidable types are decidable

```agda
is-decidable-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A × B)
is-decidable-prod (inl a) (inl b) = inl (pair a b)
is-decidable-prod (inl a) (inr g) = inr (g ∘ pr2)
is-decidable-prod (inr f) (inl b) = inr (f ∘ pr1)
is-decidable-prod (inr f) (inr g) = inr (f ∘ pr1)

is-decidable-prod' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A × B)
is-decidable-prod' (inl a) d with d a
... | inl b = inl (pair a b)
... | inr nb = inr (nb ∘ pr2)
is-decidable-prod' (inr na) d = inr (na ∘ pr1)
```

### Function types of decidable types are decidable

```agda
is-decidable-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type (inl a) (inl b) = inl (λ x → b)
is-decidable-function-type (inl a) (inr g) = inr (λ h → g (h a))
is-decidable-function-type (inr f) (inl b) = inl (ex-falso ∘ f)
is-decidable-function-type (inr f) (inr g) = inl (ex-falso ∘ f)

is-decidable-function-type' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A → B)
is-decidable-function-type' (inl a) d with d a
... | inl b = inl (λ x → b)
... | inr nb = inr (λ f → nb (f a))
is-decidable-function-type' (inr na) d = inl (ex-falso ∘ na)
```

### The negation of a decidable type is decidable

```agda
is-decidable-neg :
  {l : Level} {A : UU l} → is-decidable A → is-decidable (¬ A)
is-decidable-neg d = is-decidable-function-type d is-decidable-empty
```

### Decidable types are closed under coinhabited types; retracts, and equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-iff :
    (A → B) → (B → A) → is-decidable A → is-decidable B
  is-decidable-iff f g (inl a) = inl (f a)
  is-decidable-iff f g (inr na) = inr (λ b → na (g b))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  is-decidable-retract-of :
    A retract-of B → is-decidable B → is-decidable A
  is-decidable-retract-of (pair i (pair r H)) (inl b) = inl (r b)
  is-decidable-retract-of (pair i (pair r H)) (inr f) = inr (f ∘ i)

  is-decidable-is-equiv :
    {f : A → B} → is-equiv f → is-decidable B → is-decidable A
  is-decidable-is-equiv {f} (pair (pair g G) (pair h H)) =
    is-decidable-retract-of (pair f (pair h H))

  is-decidable-equiv :
    (e : A ≃ B) → is-decidable B → is-decidable A
  is-decidable-equiv e = is-decidable-iff (map-inv-equiv e) (map-equiv e)

is-decidable-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-decidable A → is-decidable B
is-decidable-equiv' e = is-decidable-equiv (inv-equiv e)
```

### Decidability implies double negation elimination

```agda
dn-elim-is-decidable :
  {l : Level} (P : UU l) → is-decidable P → (¬¬ P → P)
dn-elim-is-decidable P (inl x) p = x
dn-elim-is-decidable P (inr x) p = ex-falso (p x)
```

### The double negation of `is-decidable` is always provable

```agda
dn-is-decidable : {l : Level} {P : UU l} → ¬¬ (is-decidable P)
dn-is-decidable {P = P} f =
  map-neg (inr {A = P} {B = ¬ P}) f
    ( map-neg (inl {A = P} {B = ¬ P}) f)
```

### Decidable types have ε-operators

```agda
elim-trunc-Prop-is-decidable :
  {l : Level} {A : UU l} → is-decidable A → ε-operator-Hilbert A
elim-trunc-Prop-is-decidable (inl a) x = a
elim-trunc-Prop-is-decidable (inr f) x =
  ex-falso (apply-universal-property-trunc-Prop x empty-Prop f)
```

### `is-decidable` is an idempotent operation

```agda
idempotent-is-decidable :
  {l : Level} (P : UU l) → is-decidable (is-decidable P) → is-decidable P
idempotent-is-decidable P (inl (inl p)) = inl p
idempotent-is-decidable P (inl (inr np)) = inr np
idempotent-is-decidable P (inr np) = inr (λ p → np (inl p))
```

### Being inhabited or empty is a proposition

```agda
abstract
  is-prop-is-inhabited-or-empty :
    {l1 : Level} (A : UU l1) → is-prop (is-inhabited-or-empty A)
  is-prop-is-inhabited-or-empty A =
    is-prop-coprod
      ( λ t → apply-universal-property-trunc-Prop t empty-Prop)
      ( is-prop-type-trunc-Prop)
      ( is-prop-neg)

is-inhabited-or-empty-Prop : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (is-inhabited-or-empty-Prop A) = is-inhabited-or-empty A
pr2 (is-inhabited-or-empty-Prop A) = is-prop-is-inhabited-or-empty A

abstract
  is-prop-is-decidable :
    {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
  is-prop-is-decidable is-prop-A =
    is-prop-coprod intro-dn is-prop-A is-prop-neg

is-decidable-Prop :
  {l : Level} → UU-Prop l → UU-Prop l
pr1 (is-decidable-Prop P) = is-decidable (type-Prop P)
pr2 (is-decidable-Prop P) = is-prop-is-decidable (is-prop-type-Prop P)
```

### Decidability of a propositional truncation

```agda
abstract
  is-prop-is-decidable-trunc-Prop :
    {l : Level} (A : UU l) → is-prop (is-decidable (type-trunc-Prop A))
  is-prop-is-decidable-trunc-Prop A =
    is-prop-is-decidable is-prop-type-trunc-Prop
    
is-decidable-trunc-Prop : {l : Level} → UU l → UU-Prop l
pr1 (is-decidable-trunc-Prop A) = is-decidable (type-trunc-Prop A)
pr2 (is-decidable-trunc-Prop A) = is-prop-is-decidable-trunc-Prop A

is-decidable-trunc-Prop-is-merely-decidable :
  {l : Level} (A : UU l) →
  is-merely-decidable A → is-decidable (type-trunc-Prop A)
is-decidable-trunc-Prop-is-merely-decidable A =
  map-universal-property-trunc-Prop
    ( is-decidable-trunc-Prop A)
    ( f)
  where
  f : is-decidable A → type-Prop (is-decidable-trunc-Prop A)
  f (inl a) = inl (unit-trunc-Prop a)
  f (inr f) = inr (map-universal-property-trunc-Prop empty-Prop f)

is-merely-decidable-is-decidable-trunc-Prop :
  {l : Level} (A : UU l) →
  is-decidable (type-trunc-Prop A) → is-merely-decidable A
is-merely-decidable-is-decidable-trunc-Prop A (inl x) =
   apply-universal-property-trunc-Prop x
     ( is-merely-decidable-Prop A)
     ( unit-trunc-Prop ∘ inl)
is-merely-decidable-is-decidable-trunc-Prop A (inr f) =
  unit-trunc-Prop (inr (f ∘ unit-trunc-Prop))
```

### Any inhabited type is a fixed point for `is-decidable`

```agda
is-fixed-point-is-decidable-is-inhabited :
  {l : Level} {X : UU l} → type-trunc-Prop X → is-decidable X ≃ X
is-fixed-point-is-decidable-is-inhabited {l} {X} t =
  right-unit-law-coprod-is-empty X (¬ X) (is-nonempty-is-inhabited t)
```

### Raising types converves decidability

```agda
module _
  (l : Level) {l1 : Level} (A : UU l1)
  where

  is-decidable-raise : is-decidable A → is-decidable (raise l A)
  is-decidable-raise (inl p) = inl (map-raise p)
  is-decidable-raise (inr np) = inr (λ p' → np (map-inv-raise p'))
```
