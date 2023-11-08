# Well-founded orders

<details><summary>Imports</summary>
```agda
module order-theory.well-founded-orders where
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
data Acc {l1 l2} {X : UU l1} (_<_ : Rel l2 X) (x : X) : UU (l1 ⊔ l2) where
  acc : ((y : X) → y < x → Acc _<_ y) → Acc _<_ x

acc-rel-elem :
  ∀ {l1 l2} {X : UU l1} (_<_ : Rel l2 X) →
  (x : X) → Acc _<_ x →
  (y : X) → y < x → Acc _<_ y
acc-rel-elem _<_ x (acc f) y y<x = f y y<x

is-well-founded : ∀ {l1 l2} {X : UU l1} → Rel l2 X → UU (l1 ⊔ l2)
is-well-founded {X = X} R = (x : X) → Acc R x

Well-Founded-Rel : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Well-Founded-Rel l X = Σ (Rel l X) is-well-founded
```

## Properties

### Well-founded induction

```agda
ind-acc :
  ∀ {l1 l2 l3} {X : UU l1} (_<_ : Rel l2 X) →
  (P : X → UU l3) →
  (∀ x → Acc _<_ x → (∀ y → y < x → P y) → P x) →
  ∀ x → Acc _<_ x → P x
ind-acc _<_ P IH x (acc f) =
  IH x (acc f) (λ y y<x → ind-acc _<_ P IH y (f y y<x))

ind-well-founded :
  ∀ {l1 l2 l3} {X : UU l1} (R : Well-Founded-Rel l2 X) →
  (P : X → UU l3) →
  (∀ x → (∀ y → pr1 R y x → P y) → P x) →
  ∀ x → P x
ind-well-founded (_<_ , wf) P IH x =
  ind-acc _<_ P (λ x _ → IH x) x (wf x)
```

### Accessibility is a property.

```agda
module _ {l1 l2} {X : UU l1} (_<_ : Rel l2 X) where

  all-elements-equal-Acc : (x : X) → all-elements-equal (Acc _<_ x)
  all-elements-equal-Acc x (acc f) (acc f') =
    ap acc (eq-htpy (λ y → eq-htpy (λ y<x → all-elements-equal-Acc y (f y y<x) (f' y y<x))))

  is-prop-Acc : (x : X) → is-prop (Acc _<_ x)
  is-prop-Acc x =
    is-prop-all-elements-equal (all-elements-equal-Acc x)

  Acc-Prop : (x : X) → Prop (l1 ⊔ l2)
  pr1 (Acc-Prop x) = Acc _<_ x
  pr2 (Acc-Prop x) = is-prop-Acc x
```

### A well-founded relation is asymmetric (and thus irreflexive)

```agda
is-asymmetric-Acc :
  ∀ {l1 l2} {X : UU l1} (_<_ : Rel l2 X) →
  (x : X) → Acc _<_ x →
  (y : X) → x < y → ¬ (y < x)
is-asymmetric-Acc _<_ x (acc f) y x<y y<x =
  is-asymmetric-Acc _<_ y (f y y<x) x y<x x<y

is-irreflexive-Acc :
  ∀ {l1 l2} {X : UU l1} (_<_ : Rel l2 X) →
  (x : X) → Acc _<_ x → ¬ (x < x)
is-irreflexive-Acc _<_ x a x<x =
  is-asymmetric-Acc _<_ x a x x<x x<x

is-asymmetric-Well-Founded-Rel :
  ∀ {l1 l2} {X : UU l1} (R : Well-Founded-Rel l2 X) →
  is-asymmetric (pr1 R)
is-asymmetric-Well-Founded-Rel (_<_ , wf) x =
  is-asymmetric-Acc _<_ x (wf x)

is-irreflexive-Well-Founded-Rel :
  ∀ {l1 l2} {X : UU l1} (R : Well-Founded-Rel l2 X) →
  is-irreflexive (pr1 R)
is-irreflexive-Well-Founded-Rel R =
  is-irreflexive-is-asymmetric
    ( pr1 R)
    ( is-asymmetric-Well-Founded-Rel R)
```
