# Double negation elimination

```agda
module foundation.untruncated-double-negation-elimination where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

We say a type `A` satisfies
{{#concept "untruncated double negation elimination" Agda=has-double-negation-elim}}
if there is a map

```text
  ¬¬A → A
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

### If the type is a propositon, then having double negation elimination is a property

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

### The empty proposition has double negation elimination

```agda
double-negation-elim-empty : has-double-negation-elim empty
double-negation-elim-empty e = e id
```

### Empty types are double negation stable propositions

```agda
double-negation-elim-is-empty :
  {l : Level} {A : UU l} → is-empty A → has-double-negation-elim A
double-negation-elim-is-empty H q = ex-falso (q H)
```

### The unit proposition has double negation elimination

```agda
double-negation-elim-unit : has-double-negation-elim unit
double-negation-elim-unit _ = star
```

### Contractible types are double negation stable

```agda
double-negation-elim-is-contr :
  {l : Level} {A : UU l} → is-contr A → has-double-negation-elim A
double-negation-elim-is-contr H _ = center H
```

### The negation of a type has double negation elimination

```agda
double-negation-elim-neg :
  {l : Level} (A : UU l) → has-double-negation-elim (¬ A)
double-negation-elim-neg A f p = f (ev p)
```

### Function types into double negations have double negation elimination

```agda
module _
  {l1 l2 : Level} {P : UU l1} {Q : UU l2}
  where

  double-negation-elim-exp-neg-neg :
    has-double-negation-elim (P → ¬¬ Q)
  double-negation-elim-exp-neg-neg f p =
    double-negation-elim-neg
      ( ¬ Q)
      ( map-double-negation (λ (g : P → ¬¬ Q) → g p) f)

  double-negation-elim-exp :
    has-double-negation-elim Q →
    has-double-negation-elim (P → Q)
  double-negation-elim-exp H f p = H (λ nq → f (λ g → nq (g p)))
```

### Universal quantification over double negations have double negation elimination

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

### Decidable propositions are double negation stable

```text
double-negation-elim-is-decidable :
  {l : Level} {A : UU l} → is-decidable A → has-double-negation-elim A
double-negation-elim-is-decidable = double-negation-elim-is-decidable
```

### Dependent sums of types with double negation elimination over a double negation stable proposition have double negation elimination

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

### The product of two types with double negation elimination has double negation elimination

```agda
double-negation-elim-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-double-negation-elim A →
  has-double-negation-elim B →
  has-double-negation-elim (A × B)
double-negation-elim-product f g h =
  f (λ na → h (na ∘ pr1)) , g (λ nb → h (nb ∘ pr2))
```

## See also

- [The double negation modality](foundation.double-negation-modality.md)
- [Irrefutable propositions](foundation.irrefutable-propositions.md) are double
  negation connected types.
