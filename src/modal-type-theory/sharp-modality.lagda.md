# The sharp modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.sharp-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-subuniverse-induction
```

</details>

## Idea

The {{#concept "sharp modality" Agda=♯}} `♯` is an axiomatized
[monadic modality](orthogonal-factorization-systems.higher-modalities.md) that
we postulate as a right adjoint to the
[flat modality](modal-type-theory.flat-modality.md).

In this file, we postulate that `♯` is a
[modal operator](orthogonal-factorization-systems.modal-operators.md) with a
crisp elimination principle and a
[modal induction principle](orthogonal-factorization-systems.modal-induction.md).

- In the file about
  [sharp codiscrete types](modal-type-theory.sharp-codiscrete-types.md), we
  currently postulate that the [subuniverse](foundation.subuniverses.md) of
  sharp modal types has appropriate closure properties.
- In [the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md), we
  postulate that it has the appropriate relation to the flat modality, making it
  a lex modality.

Please note that there is some redundancy between the postulated axioms, and
that they are likely to change in the future.

## Postulates

```agda
postulate
  ♯ : {l : Level} (A : UU l) → UU l

  unit-sharp : {l : Level} {A : UU l} → A → ♯ A

sharp : {l : Level} (A : UU l) → UU l
sharp = ♯
```

### Crisp elimination for the sharp modality

Given a crisp element `x :: ♯ A` we recover an element of `A`. We postulate that
this construction is a crisp
[coherent inverse](foundation-core.coherently-invertible-maps.md) to the sharp
unit.

```agda
postulate
  crisp-elim-sharp :
    {@♭ l : Level} {@♭ A : UU l} → @♭ ♯ A → A

  compute-crisp-elim-sharp :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) →
    crisp-elim-sharp (unit-sharp x) ＝ x

  uniqueness-crisp-elim-sharp :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : ♯ A) →
    unit-sharp (crisp-elim-sharp x) ＝ x

  coherence-uniqueness-crisp-elim-sharp :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) →
    ( uniqueness-crisp-elim-sharp (unit-sharp x)) ＝
    ( ap unit-sharp (compute-crisp-elim-sharp x))
```

**Rewriting.** In the future we may enable rewrite rules for the computation and
uniqueness property of the crisp elimination principle for the sharp modality.

```text
  {-# REWRITE compute-crisp-elim-sharp uniqueness-crisp-elim-sharp #-}
```

### Crisp induction for the sharp modality

The
{{#concept "crisp induction principle" Disambiguation="for the sharp modality" Agda=crisp-ind-sharp}}
for the sharp modality is a crisp version of the principle that sharp codiscrete
types are local at the flat counit.

```agda
postulate
  crisp-ind-sharp :
    {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : A → UU l2) →
    ((@♭ x : A) → C x) → (x : A) → ♯ (C x)

  compute-crisp-ind-sharp :
    {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : A → UU l2)
    (f : (@♭ x : A) → C x) →
    (@♭ x : A) → crisp-ind-sharp C f x ＝ unit-sharp (f x)
```

**Rewriting.** In the future, we may enable a rewriting for the computation rule
of the crisp induction principle for the sharp modality.

```text
  {-# REWRITE compute-crisp-ind-sharp #-}
```

### Modal induction for the sharp modality

We postulate that sharp satisfies a
[modal induction principle](orthogonal-factorization-systems.modal-induction.md)
below.

**Note.** It should also be possible to construct it from the more general
`pointwise-sharp` considered below, but we leave this for future work.

```agda
postulate
  ind-sharp :
    {l1 l2 : Level} {A : UU l1} (C : ♯ A → UU l2) →
    ((x : A) → ♯ (C (unit-sharp x))) →
    (x : ♯ A) → ♯ (C x)

  compute-ind-sharp :
    {l1 l2 : Level} {A : UU l1} (C : ♯ A → UU l2)
    (f : (x : A) → ♯ (C (unit-sharp x))) →
    ind-sharp C f ∘ unit-sharp ~ f
```

### The sharp modality's action on "pointwise" type families

**TODO.** This section consists entirely of unfinished work that is not
typechecked as part of the library. This code is included as notes for future
work.

```text
postulate
  pointwise-sharp :
    {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} → (@♭ A → UU l2) → A → UU l2
```

```text
postulate
  unit-pointwise-sharp :
    {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level}
    {B : @♭ A → UU l2} (a : (@♭ x : A) → B x) →
    (x : A) → pointwise-sharp B x

  elim-pointwise-sharp :
    {@♭ l1 l2 : Level} {@♭ A : UU l1} {B : @♭ A → UU l2}
    (f : (@♭ x : A) → pointwise-sharp B x) → (@♭ x : A) → B x

  compute-pointwise-sharp :
    {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level}
    (B : A → UU l2) (x : A) → pointwise-sharp (λ a → B a) x ＝ ♯ (B x)

  {-# REWRITE compute-pointwise-sharp #-}

  compute-unit-pointwise-sharp :
    {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level}
    {B : @♭ A → UU l2} (f : (@♭ x : A) → B x)
    (@♭ x : A) → unit-pointwise-sharp f x ＝ unit-sharp (f x)

  -- {-# REWRITE compute-unit-pointwise-sharp #-}

syntax elim-pointwise-sharp (λ γ → a) ctx = let♯ γ ::= ctx in♯ a ↓↓♯
```

**Warning:** When normalizing `λ B x → unit-pointwise-sharp f x`, the rewrite
`compute-unit-pointwise-sharp` will fire turning it into `unit-sharp (f x)`,
which is ill-typed on cohesive `x : A` (and the typechecker complains).
{{#cite DavidJaz/Cohesion}} (May be outdated info)

```text
postulate
  compute-elim-pointwise-sharp :
    {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
    (@♭ f : (@♭ x : A) → pointwise-sharp B x)
    (@♭ x : A) → elim-pointwise-sharp f x ＝ crisp-elim-sharp (f x)

  {-# REWRITE compute-elim-pointwise-sharp #-}
```

#### Uncrispening contexts

```text
record
  context-uncrisp-sharp
  {@♭ l1 l2 : Level} {@♭ A : UU l1} : UU (lsuc (l1 ⊔ l2))
  where
  constructor ctx
  field
    ᶜB : A → UU l2
    ᶜf : (@♭ x : A) → ♯ (ᶜB x)
    ᶜa : A

open context-uncrisp-sharp

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  where

  uncrisp-sharp : (B : A → UU l2) (f : (@♭ x : A) → ♯ (B x)) → (x : A) → ♯ (B x)
  uncrisp-sharp B f x =
    unit-pointwise-sharp (λ γ → crisp-elim-sharp ((ᶜf γ) (ᶜa γ))) (ctx B f x)

  compute-uncrisp-sharp :
    (@♭ B : A → UU l2) (@♭ f : (@♭ x : A) → ♯ (B x)) (@♭ x : A) →
    uncrisp-sharp B f x ＝ f x
  compute-uncrisp-sharp B f x =
    compute-unit-pointwise-sharp
      ( λ γ → crisp-elim-sharp ((ᶜf γ) (ᶜa γ)))
      ( ctx B f x)

module _
  {@♭ l1 l2 l3 : Level}
  {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  uncrisp-sharp² :
    (C : (x : A) → B x → UU l3)
    (f : (@♭ x : A) (@♭ y : B x) → ♯ (C x y))
    (x : A) (y : B x) → ♯ (C x y)
  uncrisp-sharp² C f x y =
    uncrisp-sharp (λ (x , y) → C x y) (λ p → f (pr1 p) (pr2 p)) (x , y)

  compute-uncrisp-sharp² :
    (@♭ C : (x : A) → B x → UU l3)
    (@♭ f : (@♭ x : A) (@♭ y : B x) → ♯ (C x y))
    (@♭ x : A) (@♭ y : B x) → uncrisp-sharp² C f x y ＝ f x y
  compute-uncrisp-sharp² C f x y =
    compute-uncrisp-sharp (λ (x , y) → C x y) (λ p → f (pr1 p) (pr2 p)) (x , y)
```

#### Sharp induction revisited

The following definitions rely on rewrite rules.

```text
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} (@♭ C : ♯ A → UU l2)
  (@♭ f : (x : A) → ♯ (C (unit-sharp x)))
  where

  ind-sharp' : (x : ♯ A) → ♯ (C x)
  ind-sharp' =
    crisp-ind-sharp C (λ x → crisp-elim-sharp (f (crisp-elim-sharp x)))

  compute-ind-sharp' : (@♭ x : A) → ind-sharp' (unit-sharp x) ＝ f x
  compute-ind-sharp' x =
    compute-crisp-ind-sharp C
      ( λ x → crisp-elim-sharp (f (crisp-elim-sharp x)))
      ( unit-sharp x)
```

## Definitions

### The sharp modal operator

```agda
sharp-locally-small-operator-modality :
  (l : Level) → locally-small-operator-modality l l l
pr1 (sharp-locally-small-operator-modality l) = ♯
pr2 (sharp-locally-small-operator-modality l) A = is-locally-small' {l} {♯ A}
```

### The sharp modality's induction principle

```agda
induction-principle-sharp :
  {l : Level} → induction-principle-modality {l} unit-sharp
pr1 (induction-principle-sharp P) = ind-sharp P
pr2 (induction-principle-sharp P) = compute-ind-sharp P

strong-induction-principle-subuniverse-sharp :
  {l : Level} → strong-induction-principle-subuniverse-modality {l} unit-sharp
strong-induction-principle-subuniverse-sharp =
  strong-induction-principle-subuniverse-induction-principle-modality
    ( unit-sharp)
    ( induction-principle-sharp)

strong-ind-subuniverse-sharp :
  {l : Level} → strong-ind-subuniverse-modality {l} unit-sharp
strong-ind-subuniverse-sharp =
  strong-ind-strong-induction-principle-subuniverse-modality
    ( unit-sharp)
    ( strong-induction-principle-subuniverse-sharp)

compute-strong-ind-subuniverse-sharp :
  {l : Level} →
  compute-strong-ind-subuniverse-modality {l}
    unit-sharp
    strong-ind-subuniverse-sharp
compute-strong-ind-subuniverse-sharp =
  compute-strong-ind-strong-induction-principle-subuniverse-modality
    ( unit-sharp)
    ( strong-induction-principle-subuniverse-sharp)

induction-principle-subuniverse-sharp :
  {l : Level} → induction-principle-subuniverse-modality {l} unit-sharp
induction-principle-subuniverse-sharp =
  induction-principle-subuniverse-induction-principle-modality
    ( unit-sharp)
    ( induction-principle-sharp)

ind-subuniverse-sharp :
  {l : Level} → ind-subuniverse-modality {l} unit-sharp
ind-subuniverse-sharp =
  ind-induction-principle-subuniverse-modality
    ( unit-sharp)
    ( induction-principle-subuniverse-sharp)

compute-ind-subuniverse-sharp :
  {l : Level} →
  compute-ind-subuniverse-modality {l} unit-sharp ind-subuniverse-sharp
compute-ind-subuniverse-sharp =
  compute-ind-induction-principle-subuniverse-modality
    ( unit-sharp)
    ( induction-principle-subuniverse-sharp)
```

### The sharp modality's recursion principle

```agda
rec-sharp :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → ♯ B) → (♯ A → ♯ B)
rec-sharp {B = B} = ind-sharp (λ _ → B)

compute-rec-sharp :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → ♯ B) →
  (rec-sharp f ∘ unit-sharp) ~ f
compute-rec-sharp {B = B} = compute-ind-sharp (λ _ → B)

recursion-principle-sharp :
  {l : Level} → recursion-principle-modality {l} unit-sharp
pr1 (recursion-principle-sharp) = rec-sharp
pr2 (recursion-principle-sharp) = compute-rec-sharp

strong-recursion-principle-subuniverse-sharp :
  {l : Level} → strong-recursion-principle-subuniverse-modality {l} unit-sharp
strong-recursion-principle-subuniverse-sharp =
  strong-recursion-principle-subuniverse-recursion-principle-modality
    ( unit-sharp)
    ( recursion-principle-sharp)

strong-rec-subuniverse-sharp :
  {l : Level} → strong-rec-subuniverse-modality {l} unit-sharp
strong-rec-subuniverse-sharp =
  strong-rec-strong-recursion-principle-subuniverse-modality
    ( unit-sharp)
    ( strong-recursion-principle-subuniverse-sharp)

compute-strong-rec-subuniverse-sharp :
  {l : Level} →
  compute-strong-rec-subuniverse-modality {l}
    unit-sharp
    strong-rec-subuniverse-sharp
compute-strong-rec-subuniverse-sharp =
  compute-strong-rec-strong-recursion-principle-subuniverse-modality
    ( unit-sharp)
    ( strong-recursion-principle-subuniverse-sharp)

recursion-principle-subuniverse-sharp :
  {l : Level} → recursion-principle-subuniverse-modality {l} unit-sharp
recursion-principle-subuniverse-sharp =
  recursion-principle-subuniverse-recursion-principle-modality
    ( unit-sharp)
    ( recursion-principle-sharp)

rec-subuniverse-sharp :
  {l : Level} → rec-subuniverse-modality {l} unit-sharp
rec-subuniverse-sharp =
  rec-recursion-principle-subuniverse-modality
    ( unit-sharp)
    ( recursion-principle-subuniverse-sharp)

compute-rec-subuniverse-sharp :
  {l : Level} →
  compute-rec-subuniverse-modality {l} unit-sharp rec-subuniverse-sharp
compute-rec-subuniverse-sharp =
  compute-rec-recursion-principle-subuniverse-modality
    ( unit-sharp)
    ( recursion-principle-subuniverse-sharp)
```

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
{{#reference Felixwellen/DCHoTT-Agda}} {{#reference DavidJaz/Cohesion}}
