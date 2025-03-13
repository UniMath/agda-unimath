# Irrefutable equality

```agda
module foundation.irrefutable-equality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-propositional-truncation
open import foundation.reflecting-maps-equivalence-relations
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.equivalence-relations
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

Two elements `x` and `y` in a type are said to be
{{#concept "irrefutably equal" Agda=irrefutable-eq}} if there is an element of
the [double negation](foundation.double-negation.md) of the
[identity type](foundation-core.identity-types.md) between them, `¬¬ (x ＝ y)`.
If every two elements of a type are irrefutably equal, we say the type _has
double negation dense equality_.

## Definitions

```agda
module _
  {l : Level} {A : UU l}
  where

  irrefutable-eq : A → A → UU l
  irrefutable-eq x y = ¬¬ (x ＝ y)

  is-prop-irrefutable-eq : (x y : A) → is-prop (irrefutable-eq x y)
  is-prop-irrefutable-eq x y = is-prop-double-negation

  irrefutable-eq-Prop : A → A → Prop l
  irrefutable-eq-Prop x y = (irrefutable-eq x y , is-prop-irrefutable-eq x y)
```

### Types with double negation dense equality

```agda
has-double-negation-dense-equality : {l : Level} → UU l → UU l
has-double-negation-dense-equality A = (x y : A) → irrefutable-eq x y
```

## Properties

### Reflexivity

```agda
abstract
  refl-irrefutable-eq :
    {l : Level} {A : UU l} → is-reflexive (irrefutable-eq {l} {A})
  refl-irrefutable-eq _ = intro-double-negation refl

irrefutable-eq-eq :
    {l : Level} {A : UU l} {x y : A} → x ＝ y → irrefutable-eq x y
irrefutable-eq-eq = intro-double-negation
```

### Symmetry

```agda
abstract
  symmetric-irrefutable-eq :
    {l : Level} {A : UU l} → is-symmetric (irrefutable-eq {l} {A})
  symmetric-irrefutable-eq _ _ = map-double-negation inv
```

### Transitivity

```agda
abstract
  transitive-irrefutable-eq :
    {l : Level} {A : UU l} → is-transitive (irrefutable-eq {l} {A})
  transitive-irrefutable-eq x y z nnp nnq npq =
    nnp (λ p → nnq (λ q → npq (q ∙ p)))
```

### Irrefutable equality is an equivalence relation

```agda
irrefutable-eq-equivalence-relation :
  {l1 : Level} (A : UU l1) → equivalence-relation l1 A
pr1 (irrefutable-eq-equivalence-relation A) = irrefutable-eq-Prop
pr1 (pr2 (irrefutable-eq-equivalence-relation A)) = refl-irrefutable-eq
pr1 (pr2 (pr2 (irrefutable-eq-equivalence-relation A))) =
  symmetric-irrefutable-eq
pr2 (pr2 (pr2 (irrefutable-eq-equivalence-relation A))) =
  transitive-irrefutable-eq
```

### If irrefutable equality maps into the identity type of `A`, then `A` is a set

```agda
is-set-irrefutable-eq-in-id :
  {l : Level} {A : UU l} → ((x y : A) → irrefutable-eq x y → x ＝ y) → is-set A
is-set-irrefutable-eq-in-id =
  is-set-prop-in-id irrefutable-eq is-prop-irrefutable-eq refl-irrefutable-eq
```

### Retracts of types with irrefutable equality

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-double-negation-dense-equality-retract-of :
    B retract-of A →
    has-double-negation-dense-equality A →
    has-double-negation-dense-equality B
  has-double-negation-dense-equality-retract-of (i , r , R) H x y =
    map-double-negation (λ p → inv (R x) ∙ ap r p ∙ R y) (H (i x) (i y))

  has-double-negation-dense-equality-equiv :
    B ≃ A →
    has-double-negation-dense-equality A → has-double-negation-dense-equality B
  has-double-negation-dense-equality-equiv e =
    has-double-negation-dense-equality-retract-of (retract-equiv e)

  has-double-negation-dense-equality-equiv' :
    A ≃ B →
    has-double-negation-dense-equality A → has-double-negation-dense-equality B
  has-double-negation-dense-equality-equiv' e =
    has-double-negation-dense-equality-retract-of (retract-inv-equiv e)
```

### Dependent sums of types with irrefutable equality

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (mA : has-double-negation-dense-equality A)
  (mB : (x : A) → has-double-negation-dense-equality (B x))
  where

  has-double-negation-dense-equality-Σ :
    has-double-negation-dense-equality (Σ A B)
  has-double-negation-dense-equality-Σ x y =
    extend-double-negation
      ( λ p →
        map-double-negation (eq-pair-Σ p) (mB (pr1 y) (tr B p (pr2 x)) (pr2 y)))
      ( mA (pr1 x) (pr1 y))
```
