# Singleton induction

```agda
module foundation.singleton-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.transport-along-identifications
```

</details>

## Idea

**Singleton induction** on a type `A` equipped with a point `a : A` is a
principle analogous to the induction principle of the
[unit type](foundation.unit-type.md). A type satisfies singleton induction if
and only if it is [contractible](foundation-core.contractible-types.md).

Singleton induction states that given a type family `B` over `A`, to construct a
section of `B` it suffices to construct an element in `B a`.

## Definition

### Singleton induction

```agda
is-singleton :
  (l1 : Level) {l2 : Level} (A : UU l2) → A → UU (lsuc l1 ⊔ l2)
is-singleton l A a = (B : A → UU l) → section (ev-point a {B})

ind-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) →
  ({l : Level} → is-singleton l A a) → (B : A → UU l2) →
  B a → (x : A) → B x
ind-is-singleton a is-sing-A B = pr1 (is-sing-A B)

compute-ind-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) (H : {l : Level} → is-singleton l A a) →
  (B : A → UU l2) → (ev-point a {B} ∘ ind-is-singleton a H B) ~ id
compute-ind-is-singleton a H B = pr2 (H B)
```

## Properties

### Contractible types satisfy singleton induction

```agda
abstract
  ind-singleton :
    {l1 l2 : Level} {A : UU l1} (a : A) (is-contr-A : is-contr A)
    (B : A → UU l2) → B a → (x : A) → B x
  ind-singleton a is-contr-A B b x =
    tr B (inv (contraction is-contr-A a) ∙ contraction is-contr-A x) b

abstract
  compute-ind-singleton :
    {l1 l2 : Level} {A : UU l1}
    (a : A) (is-contr-A : is-contr A) (B : A → UU l2) →
    (ev-point a {B} ∘ ind-singleton a is-contr-A B) ~ id
  compute-ind-singleton a is-contr-A B b =
    ap (λ p → tr B p b) (left-inv (contraction is-contr-A a))
```

### A type satisfies singleton induction if and only if it is contractible

```agda
is-singleton-is-contr :
  {l1 l2 : Level} {A : UU l1} (a : A) → is-contr A → is-singleton l2 A a
pr1 (is-singleton-is-contr a is-contr-A B) =
  ind-singleton a is-contr-A B
pr2 (is-singleton-is-contr a is-contr-A B) =
  compute-ind-singleton a is-contr-A B

abstract
  is-contr-ind-singleton :
    {l1 : Level} (A : UU l1) (a : A) →
    ({l2 : Level} (B : A → UU l2) → B a → (x : A) → B x) → is-contr A
  pr1 (is-contr-ind-singleton A a S) = a
  pr2 (is-contr-ind-singleton A a S) = S (λ x → a ＝ x) refl

abstract
  is-contr-is-singleton :
    {l1 : Level} (A : UU l1) (a : A) →
    ({l2 : Level} → is-singleton l2 A a) → is-contr A
  is-contr-is-singleton A a S = is-contr-ind-singleton A a (pr1 ∘ S)
```

## Examples

### The total space of an identity type satisfies singleton induction

```agda
abstract
  is-singleton-total-path :
    {l1 l2 : Level} (A : UU l1) (a : A) →
    is-singleton l2 (Σ A (λ x → a ＝ x)) (a , refl)
  pr1 (is-singleton-total-path A a B) = ind-Σ ∘ ind-Id a _
  pr2 (is-singleton-total-path A a B) = refl-htpy
```

## See also

- The equivalent principle of
  [subsingleton induction](foundation.subsingleton-induction.md)
- [Singleton subsets](foundation.singleton-subtypes.md)
