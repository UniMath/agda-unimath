# Singleton induction

```agda
module foundation.singleton-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.universe-levels
```

</details>

## Idea

Singleton induction on a type `A` equipped with a point `a : A` is a principle analogous to the induction principle of the unit type. A type satisfies singleton induction if and only if it is contractible.

## Definition

```agda
is-singleton :
  (l : Level) {i : Level} (A : UU i) → A → UU (lsuc l ⊔ i)
is-singleton l A a = (B : A → UU l) → sec (ev-pt a B)

ind-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) →
  ({l : Level} → is-singleton l A a) → (B : A → UU l2) →
  B a → (x : A) → B x
ind-is-singleton a is-sing-A B = pr1 (is-sing-A B)

comp-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) (H : {l : Level} → is-singleton l A a) →
  (B : A → UU l2) → (ev-pt a B ∘ ind-is-singleton a H B) ~ id
comp-is-singleton a H B = pr2 (H B)
```

## Properties

### A type satisfies singleton induction if and only if it is contractible

```agda
abstract
  ind-singleton-is-contr :
    {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
    B a → (x : A) → B x
  ind-singleton-is-contr a is-contr-A B b x =
    tr B ((inv (contraction is-contr-A a)) ∙ (contraction is-contr-A x)) b

  comp-singleton-is-contr :
    {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
    ((ev-pt a B) ∘ (ind-singleton-is-contr a is-contr-A B)) ~ id
  comp-singleton-is-contr a is-contr-A B b =
    ap (λ ω → tr B ω b) (left-inv (contraction is-contr-A a))

is-singleton-is-contr :
  {l1 l2 : Level} {A : UU l1} (a : A) → is-contr A → is-singleton l2 A a
pr1 (is-singleton-is-contr a is-contr-A B) =
  ind-singleton-is-contr a is-contr-A B
pr2 (is-singleton-is-contr a is-contr-A B) =
  comp-singleton-is-contr a is-contr-A B

abstract
  is-contr-ind-singleton :
    {i : Level} (A : UU i) (a : A) →
    ({l : Level} (P : A → UU l) → P a → (x : A) → P x) → is-contr A
  pr1 (is-contr-ind-singleton A a S) = a
  pr2 (is-contr-ind-singleton A a S) = S (λ x → a ＝ x) refl

abstract
  is-contr-is-singleton :
    {i : Level} (A : UU i) (a : A) →
    ({l : Level} → is-singleton l A a) → is-contr A
  is-contr-is-singleton A a S = is-contr-ind-singleton A a (λ P → pr1 (S P))
```

## Examples

### The total space of an identity type satisfies singleton induction

```agda
abstract
  is-singleton-total-path :
    {i l : Level} (A : UU i) (a : A) →
    is-singleton l (Σ A (λ x → a ＝ x)) (pair a refl)
  pr1 (is-singleton-total-path A a B) = ind-Σ ∘ (ind-Id a _)
  pr2 (is-singleton-total-path A a B) = refl-htpy
```
