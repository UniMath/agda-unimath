# Weak function extensionality

```agda
module foundation.weak-function-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

**Weak function extensionality** is the principle that any dependent product of
[contractible types](foundation-core.contractible-types.md) is contractible.
This principle is [equivalent](foundation-core.equivalences.md) to
[the function extensionality axiom](foundation-core.function-extensionality.md).

## Definition

### Weak function extensionality

```agda
WEAK-FUNEXT :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
WEAK-FUNEXT A B =
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
```

### Weaker function extensionality

```agda
WEAKER-FUNEXT :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
WEAKER-FUNEXT A B =
  ((x : A) → is-prop (B x)) → is-prop ((x : A) → B x)
```

## Properties

### Weak function extensionality is logically equivalent to function extensionality

```agda
abstract
  weak-funext-funext :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f) →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B)
  pr1 (weak-funext-funext funext A B is-contr-B) x =
    center (is-contr-B x)
  pr2 (weak-funext-funext funext A B is-contr-B) f =
    map-inv-is-equiv
      ( funext A B (λ x → center (is-contr-B x)) f)
      ( λ x → contraction (is-contr-B x) (f x))

abstract
  funext-weak-funext :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B) →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f)
  funext-weak-funext weak-funext A B f =
    fundamental-theorem-id
      ( is-contr-retract-of
        ( (x : A) → Σ (B x) (λ b → f x ＝ b))
        ( ( λ t x → (pr1 t x , pr2 t x)) ,
          ( λ t → (pr1 ∘ t , pr2 ∘ t)) ,
          ( λ t → eq-pair-Σ refl refl))
        ( weak-funext A
          ( λ x → Σ (B x) (λ b → f x ＝ b))
          ( λ x → is-contr-total-path (f x))))
      ( λ g → htpy-eq {g = g})
```

### A partial converse to weak function extensionality

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2}
  (d : has-decidable-equality I)
  (H : is-contr ((i : I) → A i))
  where

  cases-function-converse-weak-funext :
    (i : I) (x : A i) (j : I) (e : is-decidable (i ＝ j)) → A j
  cases-function-converse-weak-funext i x .i (inl refl) = x
  cases-function-converse-weak-funext i x j (inr f) = center H j

  function-converse-weak-funext :
    (i : I) (x : A i) (j : I) → A j
  function-converse-weak-funext i x j =
    cases-function-converse-weak-funext i x j (d i j)

  cases-eq-function-converse-weak-funext :
    (i : I) (x : A i) (e : is-decidable (i ＝ i)) →
    cases-function-converse-weak-funext i x i e ＝ x
  cases-eq-function-converse-weak-funext i x (inl p) =
    ap
      ( λ t → cases-function-converse-weak-funext i x i (inl t))
      ( eq-is-prop
        ( is-set-has-decidable-equality d i i)
        { p}
        { refl})
  cases-eq-function-converse-weak-funext i x (inr f) =
    ex-falso (f refl)

  eq-function-converse-weak-funext :
    (i : I) (x : A i) →
    function-converse-weak-funext i x i ＝ x
  eq-function-converse-weak-funext i x =
    cases-eq-function-converse-weak-funext i x (d i i)

  converse-weak-funext : (i : I) → is-contr (A i)
  pr1 (converse-weak-funext i) = center H i
  pr2 (converse-weak-funext i) y =
    ( htpy-eq
      ( contraction H (function-converse-weak-funext i y))
      ( i)) ∙
    ( eq-function-converse-weak-funext i y)
```

### Weaker function extensionality implies weak function extensionality

```agda
weak-funext-weaker-funext :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  WEAKER-FUNEXT A B → WEAK-FUNEXT A B
weak-funext-weaker-funext H C =
  is-proof-irrelevant-is-prop
    ( H (λ x → is-prop-is-contr (C x)))
    ( λ x → center (C x))
```
