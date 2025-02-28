# Double negation elimination

```agda
module logic.double-negation-elimination where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.evaluation-functions
open import foundation.hilberts-epsilon-operators
open import foundation.logical-equivalences
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

We say a type `A` satisfies
{{#concept "untruncated double negation elimination" Disambiguation="on a type" Agda=has-double-negation-elim}}
if there is a map

```text
  ¬¬A → A.
```

## Definitions

### Untruncated double negation elimination

```agda
module _
  {l : Level} (A : UU l)
  where

  has-double-negation-elim : UU l
  has-double-negation-elim = ¬¬ A → A
```

## Properties

### Having double negation elimination is a property for propositions

```agda
is-prop-has-double-negation-elim :
  {l : Level} {A : UU l} → is-prop A → is-prop (has-double-negation-elim A)
is-prop-has-double-negation-elim = is-prop-function-type
```

### Double negation elimination is preserved by logical equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-double-negation-elim-iff :
    A ↔ B → has-double-negation-elim B → has-double-negation-elim A
  has-double-negation-elim-iff e H =
    backward-implication e ∘ H ∘ map-double-negation (forward-implication e)

  has-double-negation-elim-iff' :
    B ↔ A → has-double-negation-elim B → has-double-negation-elim A
  has-double-negation-elim-iff' e = has-double-negation-elim-iff (inv-iff e)
```

### Double negation elimination is preserved by equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-double-negation-elim-equiv :
    A ≃ B → has-double-negation-elim B → has-double-negation-elim A
  has-double-negation-elim-equiv e =
    has-double-negation-elim-iff (iff-equiv e)

  has-double-negation-elim-equiv' :
    B ≃ A → has-double-negation-elim B → has-double-negation-elim A
  has-double-negation-elim-equiv' e =
    has-double-negation-elim-iff' (iff-equiv e)
```

### Double negation elimination is preserved by retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-double-negation-elim-retract :
    A retract-of B → has-double-negation-elim B → has-double-negation-elim A
  has-double-negation-elim-retract e =
    has-double-negation-elim-iff (iff-retract e)

  has-double-negation-elim-retract' :
    B retract-of A → has-double-negation-elim B → has-double-negation-elim A
  has-double-negation-elim-retract' e =
    has-double-negation-elim-iff' (iff-retract e)
```

### If the negation of a type with double negation elimination is decidable, then the type is decidable

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-decidable-is-decidable-neg-has-double-negation-elim :
    has-double-negation-elim A → is-decidable (¬ A) → is-decidable A
  is-decidable-is-decidable-neg-has-double-negation-elim f (inl nx) =
    inr nx
  is-decidable-is-decidable-neg-has-double-negation-elim f (inr nnx) =
    inl (f nnx)
```

**Remark.** It is an established fact that both the property of satisfying
double negation elimination, and the property of having decidable negation, are
strictly weaker conditions than being decidable. Therefore, this result
demonstrates that they are independent too.

### Double negation elimination for empty types

```agda
double-negation-elim-empty : has-double-negation-elim empty
double-negation-elim-empty e = e id

double-negation-elim-is-empty :
  {l : Level} {A : UU l} → is-empty A → has-double-negation-elim A
double-negation-elim-is-empty H q = ex-falso (q H)
```

### Double negation elimination for the unit type

```agda
double-negation-elim-unit : has-double-negation-elim unit
double-negation-elim-unit _ = star
```

### Double negation elimination for contractible types

```agda
double-negation-elim-is-contr :
  {l : Level} {A : UU l} → is-contr A → has-double-negation-elim A
double-negation-elim-is-contr H _ = center H
```

### Double negation elimination for negations of types

```agda
double-negation-elim-neg :
  {l : Level} (A : UU l) → has-double-negation-elim (¬ A)
double-negation-elim-neg A f p = f (ev p)
```

### Double negation elimination for universal quantification over double negations

```agda
module _
  {l1 l2 : Level} {P : UU l1} {Q : P → UU l2}
  where

  double-negation-elim-for-all-neg-neg :
    has-double-negation-elim ((p : P) → ¬¬ (Q p))
  double-negation-elim-for-all-neg-neg f p =
    double-negation-elim-neg
      ( ¬ (Q p))
      ( map-double-negation (λ (g : (u : P) → ¬¬ (Q u)) → g p) f)

  double-negation-elim-for-all :
    ((p : P) → has-double-negation-elim (Q p)) →
    has-double-negation-elim ((p : P) → Q p)
  double-negation-elim-for-all H f p = H p (λ nq → f (λ g → nq (g p)))
```

### Double negation elimination for function types into double negations

```agda
module _
  {l1 l2 : Level} {P : UU l1} {Q : UU l2}
  where

  double-negation-elim-exp-neg-neg :
    has-double-negation-elim (P → ¬¬ Q)
  double-negation-elim-exp-neg-neg =
    double-negation-elim-for-all-neg-neg

  double-negation-elim-exp :
    has-double-negation-elim Q →
    has-double-negation-elim (P → Q)
  double-negation-elim-exp q = double-negation-elim-for-all (λ _ → q)
```

### Double negation elimination for dependent sums of types with double negation elimination over a double negation stable proposition

```agda
double-negation-elim-Σ-is-prop-base :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-prop A →
  has-double-negation-elim A →
  ((a : A) → has-double-negation-elim (B a)) →
  has-double-negation-elim (Σ A B)
double-negation-elim-Σ-is-prop-base {B = B} is-prop-A f g h =
  ( f (λ na → h (na ∘ pr1))) ,
  ( g ( f (λ na → h (na ∘ pr1)))
      ( λ nb → h (λ y → nb (tr B (eq-is-prop is-prop-A) (pr2 y)))))

double-negation-elim-Σ-is-decidable-prop-base :
  {l1 l2 : Level} {P : UU l1} {B : P → UU l2} →
  is-decidable-prop P →
  ((x : P) → has-double-negation-elim (B x)) →
  has-double-negation-elim (Σ P B)
double-negation-elim-Σ-is-decidable-prop-base (H , d) =
  double-negation-elim-Σ-is-prop-base H (double-negation-elim-is-decidable d)
```

### Double negation elimination for products of types with double negation elimination

```agda
double-negation-elim-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-double-negation-elim A →
  has-double-negation-elim B →
  has-double-negation-elim (A × B)
double-negation-elim-product f g h =
  f (λ na → h (na ∘ pr1)) , g (λ nb → h (nb ∘ pr2))
```

### If a type satisfies untruncated double negation elimination then it has a Hilbert ε-operator

```agda
ε-operator-Hilbert-has-double-negation-elim :
  {l1 : Level} {A : UU l1} →
  has-double-negation-elim A →
  ε-operator-Hilbert A
ε-operator-Hilbert-has-double-negation-elim {A = A} H =
  H ∘ double-negation-double-negation-type-trunc-Prop A ∘ intro-double-negation
```

## See also

- [The double negation modality](foundation.double-negation-modality.md)
- [Irrefutable propositions](foundation.irrefutable-propositions.md) are double
  negation connected types.
