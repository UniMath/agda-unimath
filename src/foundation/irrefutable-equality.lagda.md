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
{{#concept "irrefutably equal" Disambiguation="elements of a type" Agda=irrefutable-eq}}
if there is an element of the [double negation](foundation.double-negation.md)
of the [identity type](foundation-core.identity-types.md) between them,
`¬¬ (x ＝ y)`.

## Definitions

### Irrefutably equal elements

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

**Terminology.** The term _dense_ used here is in the sense of dense with
respect to a
[reflective subuniverse](orthogonal-factorization-systems.reflective-global-subuniverses.md)/[modality](orthogonal-factorization-systems.higher-modalities.md),
or connected. Here, it means that the double negation of the identity types of
the relevant type are contractible. Since negations are propositions, it thus
suffices that the double negation has an element.

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
irrefutable-eq-equivalence-relation A =
  ( irrefutable-eq-Prop ,
    refl-irrefutable-eq ,
    symmetric-irrefutable-eq ,
    transitive-irrefutable-eq)
```

### If irrefutable equality maps into the identity type of `A`, then `A` is a set

```agda
is-set-irrefutable-eq-in-id :
  {l : Level} {A : UU l} → ((x y : A) → irrefutable-eq x y → x ＝ y) → is-set A
is-set-irrefutable-eq-in-id =
  is-set-prop-in-id irrefutable-eq is-prop-irrefutable-eq refl-irrefutable-eq
```

## See also

- [_Double negation dense equality_](foundation.double-negation-dense-equality.md)
  is the property that all elements of a type are irrefutably equal.
