# Well-founded orders

```agda
module order-theory.well-founded-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Given a type `X` with a binary relation `_<_ : X → X → Type` we say that `x : X` is accessible if `y` is accessible for all `y < x`. The relation `_<_` is well-founded if all elements of `X` are accessible.

We can use well-founded induction on a type with a well-founded relation: if from `(y : Y) → y < x → P y` we can prove `P x`, then `(x : X) → P x`.

## Definition

```agda
data Accessible-Relation {l1 l2} {X : UU l1} (_<_ : Relation l2 X) (x : X) : UU (l1 ⊔ l2) where
  accessible : ((y : X) → y < x → Accessible-Relation _<_ y) → Accessible-Relation _<_ x

accessible-rel-elem :
  ∀ {l1 l2} {X : UU l1} (_<_ : Relation l2 X) →
  (x : X) → Accessible-Relation _<_ x →
  (y : X) → y < x → Accessible-Relation _<_ y
accessible-rel-elem _<_ x (accessible f) y y<x = f y y<x

is-well-founded : ∀ {l1 l2} {X : UU l1} → Relation l2 X → UU (l1 ⊔ l2)
is-well-founded {X = X} R = (x : X) → Accessible-Relation R x

Well-Founded-Relation : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Well-Founded-Relation l X = Σ (Relation l X) is-well-founded
```

## Properties

### Well-founded induction

```agda
ind-accessible :
  ∀ {l1 l2 l3} {X : UU l1} (_<_ : Relation l2 X) →
  (P : X → UU l3) →
  (∀ x → Accessible-Relation _<_ x → (∀ y → y < x → P y) → P x) →
  ∀ x → Accessible-Relation _<_ x → P x
ind-accessible _<_ P IH x (accessible f) =
  IH x (accessible f) (λ y y<x → ind-accessible _<_ P IH y (f y y<x))

ind-well-founded :
  ∀ {l1 l2 l3} {X : UU l1} (R : Well-Founded-Relation l2 X) →
  (P : X → UU l3) →
  (∀ x → (∀ y → pr1 R y x → P y) → P x) →
  ∀ x → P x
ind-well-founded (_<_ , wf) P IH x =
  ind-accessible _<_ P (λ x _ → IH x) x (wf x)
```

### Accessibility is a property.

```agda
module _ {l1 l2} {X : UU l1} (_<_ : Relation l2 X) where

  all-elements-equal-Accessible-Relation : (x : X) → all-elements-equal (Accessible-Relation _<_ x)
  all-elements-equal-Accessible-Relation x (accessible f) (accessible f') =
    ap accessible (eq-htpy (λ y → eq-htpy (λ y<x → all-elements-equal-Accessible-Relation y (f y y<x) (f' y y<x))))

  is-prop-Accessible-Relation : (x : X) → is-prop (Accessible-Relation _<_ x)
  is-prop-Accessible-Relation x =
    is-prop-all-elements-equal (all-elements-equal-Accessible-Relation x)

  Accessible-Relation-Prop : (x : X) → Prop (l1 ⊔ l2)
  pr1 (Accessible-Relation-Prop x) = Accessible-Relation _<_ x
  pr2 (Accessible-Relation-Prop x) = is-prop-Accessible-Relation x
```

### A well-founded relation is asymmetric (and thus irreflexive)

```agda
is-asymmetric-Accessible-Relation :
  ∀ {l1 l2} {X : UU l1} (_<_ : Relation l2 X) →
  (x : X) → Accessible-Relation _<_ x →
  (y : X) → x < y → ¬ (y < x)
is-asymmetric-Accessible-Relation _<_ x (accessible f) y x<y y<x =
  is-asymmetric-Accessible-Relation _<_ y (f y y<x) x y<x x<y

is-irreflexive-Accessible-Relation :
  ∀ {l1 l2} {X : UU l1} (_<_ : Relation l2 X) →
  (x : X) → Accessible-Relation _<_ x → ¬ (x < x)
is-irreflexive-Accessible-Relation _<_ x a x<x =
  is-asymmetric-Accessible-Relation _<_ x a x x<x x<x

is-asymmetric-Well-Founded-Relation :
  ∀ {l1 l2} {X : UU l1} (R : Well-Founded-Relation l2 X) →
  is-asymmetric (pr1 R)
is-asymmetric-Well-Founded-Relation (_<_ , wf) x =
  is-asymmetric-Accessible-Relation _<_ x (wf x)

is-irreflexive-Well-Founded-Relation :
  ∀ {l1 l2} {X : UU l1} (R : Well-Founded-Relation l2 X) →
  is-irreflexive (pr1 R)
is-irreflexive-Well-Founded-Relation R =
  is-irreflexive-is-asymmetric
    ( pr1 R)
    ( is-asymmetric-Well-Founded-Relation R)
```
