# Double negation dense equality

```agda
module foundation.double-negation-dense-equality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.irrefutable-equality
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

A type `A` is said to have
{{#concept "double negation dense equality" Agda=has-double-negation-dense-equality}}
if for every two elements `x` and `y` in `A`, it is
[irrefutable](logic.irrefutable-types.md) that `x` and `y` are
[equal](foundation-core.identity-types.md). In other words, if all elements of
`A` are [irrefutably equal](foundation.irrefutable-equality.md).

**Terminology.** The term _dense_ used here is in the sense of dense with
respect to a
[reflective subuniverse](orthogonal-factorization-systems.reflective-global-subuniverses.md)/[modality](orthogonal-factorization-systems.higher-modalities.md),
or connected. Here, it means that the double negation of the identity types of
the relevant type are contractible. Since negations are propositions, it
suffices that the double negation has an element.

## Definitions

### Types with double negation dense equality

```agda
has-double-negation-dense-equality : {l : Level} → UU l → UU l
has-double-negation-dense-equality A = (x y : A) → irrefutable-eq x y
```

## Properties

### Retracts of types with double negation dense equality

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

### Dependent sums of types with double negation dense equality

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
