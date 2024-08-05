# Sharp codiscrete types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.sharp-codiscrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-equivalences
open import foundation.universe-levels

open import modal-type-theory.sharp-modality

open import orthogonal-factorization-systems.higher-modalities
open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

A type is said to be {{#concept "sharp codiscrete" Agda=is-sharp-codiscrete}} if
it is [sharp](modal-type-theory.sharp-modality.md) modal, i.e. if the sharp unit
is an [equivalence](foundation-core.equivalences.md) at that type.

We postulate that codiscrete types are closed under

- the formation of identity types
- the formation of dependent function types
- the formation of the subuniverse of codiscrete types.

Please note that there is some redundancy between the axioms that are assumed
here and in the files on
[the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md), and the
file on the [sharp modality](modal-type-theory.sharp-modality.md), and they may
be subject to change in the future.

## Definitions

### Sharp codiscrete types

```agda
module _
  {l : Level} (A : UU l)
  where

  is-sharp-codiscrete : UU l
  is-sharp-codiscrete = is-modal unit-sharp A

  is-sharp-codiscrete-Prop : Prop l
  is-sharp-codiscrete-Prop = is-modal-Prop unit-sharp A

  is-property-is-sharp-codiscrete : is-prop is-sharp-codiscrete
  is-property-is-sharp-codiscrete = is-property-is-modal unit-sharp A
```

### Sharp codiscrete families

```agda
is-sharp-codiscrete-family :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
is-sharp-codiscrete-family {A = A} B = (x : A) → is-sharp-codiscrete (B x)

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-sharp-codiscrete-family-Prop : Prop (l1 ⊔ l2)
  is-sharp-codiscrete-family-Prop = Π-Prop A (is-sharp-codiscrete-Prop ∘ B)

  is-property-is-sharp-codiscrete-family :
    is-prop (is-sharp-codiscrete-family B)
  is-property-is-sharp-codiscrete-family =
    is-prop-type-Prop is-sharp-codiscrete-family-Prop
```

### The subuniverse of sharp codiscrete types

```agda
Sharp-Codiscrete-Type : (l : Level) → UU (lsuc l)
Sharp-Codiscrete-Type l = Σ (UU l) (is-sharp-codiscrete)

module _
  {l : Level} (A : Sharp-Codiscrete-Type l)
  where

  type-Sharp-Codiscrete-Type : UU l
  type-Sharp-Codiscrete-Type = pr1 A

  is-sharp-codiscrete-type-Sharp-Codiscrete-Type :
    is-sharp-codiscrete type-Sharp-Codiscrete-Type
  is-sharp-codiscrete-type-Sharp-Codiscrete-Type = pr2 A
```

### Crisp induction for sharp codiscrete types

The following is Theorem 3.3 in {{#cite Shu18}}.

```agda
crisp-ind-sharp-codiscrete :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : A → UU l2) →
  ((x : A) → is-sharp-codiscrete (C x)) →
  ((@♭ x : A) → C x) → (x : A) → C x
crisp-ind-sharp-codiscrete C is-codisc-C f x =
  map-inv-is-equiv (is-codisc-C x) (crisp-ind-sharp C f x)

compute-crisp-ind-sharp-codiscrete :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : A → UU l2)
  (is-codisc-C : (x : A) → is-sharp-codiscrete (C x))
  (f : (@♭ x : A) → C x) →
  (@♭ x : A) → crisp-ind-sharp-codiscrete C is-codisc-C f x ＝ f x
compute-crisp-ind-sharp-codiscrete C is-codisc-C f x =
  ( ap (map-inv-is-equiv (is-codisc-C x)) (compute-crisp-ind-sharp C f x)) ∙
  ( is-retraction-map-inv-is-equiv (is-codisc-C x) (f x))
```

## Postulates

### The identity types of `♯ A` are sharp codiscrete

```agda
postulate
  is-sharp-codiscrete-Id-sharp :
    {l1 : Level} {A : UU l1} (x y : ♯ A) → is-sharp-codiscrete (x ＝ y)

is-sharp-codiscrete-Id :
  {l1 : Level} {A : UU l1} (x y : A) →
  is-sharp-codiscrete A → is-sharp-codiscrete (x ＝ y)
is-sharp-codiscrete-Id x y is-sharp-A =
  map-tr-equiv
    ( is-sharp-codiscrete)
    ( inv-equiv-ap-is-emb (is-emb-is-equiv is-sharp-A))
    ( is-sharp-codiscrete-Id-sharp (unit-sharp x) (unit-sharp y))
```

### A dependent function type is codiscrete if its codomain is

```agda
postulate
  is-sharp-codiscrete-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-sharp-codiscrete (B x)) →
    is-sharp-codiscrete ((x : A) → B x)

is-sharp-codiscrete-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-sharp-codiscrete B →
  is-sharp-codiscrete (A → B)
is-sharp-codiscrete-function-type is-sharp-B =
  is-sharp-codiscrete-Π (λ _ → is-sharp-B)
```

### The universe of codiscrete types is codiscrete

```agda
postulate
  is-sharp-codiscrete-Sharp-Codiscrete-Type :
    (l : Level) → is-sharp-codiscrete (Sharp-Codiscrete-Type l)
```

### The sharp higher modality

```agda
module _
  (l : Level)
  where

  is-higher-modality-sharp :
    is-higher-modality (sharp-locally-small-operator-modality l) (unit-sharp)
  pr1 is-higher-modality-sharp = induction-principle-sharp
  pr2 is-higher-modality-sharp X = is-sharp-codiscrete-Id-sharp

  sharp-higher-modality : higher-modality l l
  pr1 sharp-higher-modality = sharp-locally-small-operator-modality l
  pr1 (pr2 sharp-higher-modality) = unit-sharp
  pr2 (pr2 sharp-higher-modality) = is-higher-modality-sharp
```

### Iterated crisp induction for sharp codiscrete types

```agda
module _
  {@♭ l1 l2 : Level} {l3 : Level}
  {@♭ A : UU l1} {@♭ B : A → UU l2} (C : (x : A) → B x → UU l3)
  (is-codisc-C : (x : A) (y : B x) → is-sharp-codiscrete (C x y))
  (f : (@♭ x : A) (@♭ y : B x) → C x y)
  where

  crisp-binary-ind-sharp-codiscrete : (x : A) (y : B x) → C x y
  crisp-binary-ind-sharp-codiscrete =
    crisp-ind-sharp-codiscrete
      ( λ x → (y : B x) → C x y)
      ( λ x → is-sharp-codiscrete-Π (is-codisc-C x))
      ( λ x → crisp-ind-sharp-codiscrete (C x) (is-codisc-C x) (f x))

  compute-crisp-binary-ind-sharp-codiscrete :
    (@♭ x : A) (@♭ y : B x) → crisp-binary-ind-sharp-codiscrete x y ＝ f x y
  compute-crisp-binary-ind-sharp-codiscrete x y =
    ( htpy-eq
      ( compute-crisp-ind-sharp-codiscrete
        ( λ x → (y : B x) → C x y)
        ( λ x → is-sharp-codiscrete-Π (is-codisc-C x))
        ( λ x → crisp-ind-sharp-codiscrete (C x) (is-codisc-C x) (f x))
        ( x))
      ( y)) ∙
    ( compute-crisp-ind-sharp-codiscrete (C x) (is-codisc-C x) (f x) y)

module _
  {@♭ l1 l2 l3 : Level} {l4 : Level}
  {@♭ A : UU l1} {@♭ B : A → UU l2} {@♭ C : (x : A) → B x → UU l3}
  (D : (x : A) (y : B x) → C x y → UU l4)
  (is-codisc-D : (x : A) (y : B x) (z : C x y) → is-sharp-codiscrete (D x y z))
  (f : (@♭ x : A) (@♭ y : B x) (@♭ z : C x y) → D x y z)
  where

  crisp-ternary-ind-sharp-codiscrete : (x : A) (y : B x) (z : C x y) → D x y z
  crisp-ternary-ind-sharp-codiscrete =
    crisp-ind-sharp-codiscrete
      ( λ x → (y : B x) (z : C x y) → D x y z)
      ( λ x →
        is-sharp-codiscrete-Π (λ y → is-sharp-codiscrete-Π (is-codisc-D x y)))
      ( λ x → crisp-binary-ind-sharp-codiscrete (D x) (is-codisc-D x) (f x))

  compute-crisp-ternary-ind-sharp-codiscrete :
    (@♭ x : A) (@♭ y : B x) (@♭ z : C x y) →
    crisp-ternary-ind-sharp-codiscrete x y z ＝ f x y z
  compute-crisp-ternary-ind-sharp-codiscrete x y z =
    ( htpy-eq
      ( htpy-eq
        ( compute-crisp-ind-sharp-codiscrete
          ( λ x → (y : B x) (z : C x y) → D x y z)
          ( λ x →
            is-sharp-codiscrete-Π
              ( λ y → is-sharp-codiscrete-Π (is-codisc-D x y)))
          ( λ x → crisp-binary-ind-sharp-codiscrete (D x) (is-codisc-D x) (f x))
          ( x))
        ( y))
      ( z)) ∙
    ( compute-crisp-binary-ind-sharp-codiscrete (D x) (is-codisc-D x) (f x) y z)
```

## Properties

### Types in the image of the sharp modality are codiscrete

```agda
is-sharp-codiscrete-sharp : {l : Level} (X : UU l) → is-sharp-codiscrete (♯ X)
is-sharp-codiscrete-sharp {l} =
  is-modal-operator-type-higher-modality (sharp-higher-modality l)
```

## See also

- [Flat discrete crisp types](modal-type-theory.flat-discrete-crisp-types.md)
  for a partial dual notion.
