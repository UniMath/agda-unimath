# Decidable subtypes of finite types

```agda
module univalent-combinatorics.decidable-subtypes where

open import foundation.decidable-subtypes public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.embeddings
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import univalent-combinatorics.decidable-dependent-pair-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
```

</details>

## Definitions

### Finite subsets of a finite set

```agda
subset-Finite-Type :
  {l1 : Level} (l2 : Level) → Finite-Type l1 → UU (l1 ⊔ lsuc l2)
subset-Finite-Type l2 X = decidable-subtype l2 (type-Finite-Type X)

module _
  {l1 l2 : Level} (X : Finite-Type l1) (P : subset-Finite-Type l2 X)
  where

  subtype-subset-Finite-Type : subtype l2 (type-Finite-Type X)
  subtype-subset-Finite-Type = subtype-decidable-subtype P

  is-decidable-subset-Finite-Type :
    is-decidable-subtype subtype-subset-Finite-Type
  is-decidable-subset-Finite-Type =
    is-decidable-decidable-subtype P

  is-in-subset-Finite-Type : type-Finite-Type X → UU l2
  is-in-subset-Finite-Type = is-in-decidable-subtype P

  is-prop-is-in-subset-Finite-Type :
    (x : type-Finite-Type X) → is-prop (is-in-subset-Finite-Type x)
  is-prop-is-in-subset-Finite-Type = is-prop-is-in-decidable-subtype P
```

### The underlying type of a decidable subtype

```agda
module _
  {l1 l2 : Level} (X : Finite-Type l1) (P : subset-Finite-Type l2 X)
  where

  type-subset-Finite-Type : UU (l1 ⊔ l2)
  type-subset-Finite-Type = type-decidable-subtype P

  inclusion-subset-Finite-Type : type-subset-Finite-Type → type-Finite-Type X
  inclusion-subset-Finite-Type = inclusion-decidable-subtype P

  is-emb-inclusion-subset-Finite-Type : is-emb inclusion-subset-Finite-Type
  is-emb-inclusion-subset-Finite-Type = is-emb-inclusion-decidable-subtype P

  is-injective-inclusion-subset-Finite-Type :
    is-injective inclusion-subset-Finite-Type
  is-injective-inclusion-subset-Finite-Type =
    is-injective-inclusion-decidable-subtype P

  emb-subset-Finite-Type : type-subset-Finite-Type ↪ type-Finite-Type X
  emb-subset-Finite-Type = emb-decidable-subtype P
```

## Properties

### The type of decidable subtypes of a finite type is finite

The computation of the number of subsets of a finite sets is the
[52nd](literature.100-theorems.md#52) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
is-finite-decidable-subtype-is-finite :
  {l1 l2 : Level} {X : UU l1} →
  is-finite X → is-finite (decidable-subtype l2 X)
is-finite-decidable-subtype-is-finite H =
  is-finite-function-type H is-finite-Decidable-Prop

number-of-elements-decidable-subtype-is-finite :
  {l1 l2 : Level} {X : UU l1} (H : is-finite X) →
  number-of-elements-is-finite
    ( is-finite-decidable-subtype-is-finite {l2 = l2} H) ＝
  exp-ℕ 2 (number-of-elements-is-finite H)
number-of-elements-decidable-subtype-is-finite {l1} {l2} H =
  number-of-elements-function-type H is-finite-Decidable-Prop ∙
  ap
    ( λ x → exp-ℕ x (number-of-elements-is-finite H))
    ( number-of-elements-Decidable-Prop {l2})

Subset-Finite-Type :
  {l1 : Level} (l2 : Level) → Finite-Type l1 → Finite-Type (l1 ⊔ lsuc l2)
pr1 (Subset-Finite-Type l2 X) = subset-Finite-Type l2 X
pr2 (Subset-Finite-Type l2 X) =
  is-finite-decidable-subtype-is-finite (is-finite-type-Finite-Type X)
```

### The type of decidable subsets of a finite type has decidable equality

```agda
has-decidable-equality-Subset-Finite-Type :
  {l1 l2 : Level} (X : Finite-Type l1) →
  has-decidable-equality (decidable-subtype l2 (type-Finite-Type X))
has-decidable-equality-Subset-Finite-Type {l1} {l2} X =
  has-decidable-equality-is-finite
    ( is-finite-decidable-subtype-is-finite (is-finite-type-Finite-Type X))
```

### Decidable subtypes of finite types are finite

```agda
is-finite-type-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X) →
    is-finite X → is-finite (type-decidable-subtype P)
is-finite-type-decidable-subtype P H =
  is-finite-Σ H
    ( λ x →
      is-finite-is-decidable-Prop
        ( prop-Decidable-Prop (P x))
        ( is-decidable-Decidable-Prop (P x)))

is-finite-type-subset-Finite-Type :
  {l1 l2 : Level} (X : Finite-Type l1) (P : subset-Finite-Type l2 X) →
  is-finite (type-subset-Finite-Type X P)
is-finite-type-subset-Finite-Type X P =
  is-finite-type-decidable-subtype P (is-finite-type-Finite-Type X)

finite-type-subset-Finite-Type :
  {l1 l2 : Level} (X : Finite-Type l1) →
  subset-Finite-Type l2 X → Finite-Type (l1 ⊔ l2)
pr1 (finite-type-subset-Finite-Type X P) = type-subset-Finite-Type X P
pr2 (finite-type-subset-Finite-Type X P) = is-finite-type-subset-Finite-Type X P
```

### The underlying type of a decidable subtype has decidable equality

```agda
has-decidable-equality-type-decidable-subtype-is-finite :
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X) → is-finite X →
  has-decidable-equality (type-decidable-subtype P)
has-decidable-equality-type-decidable-subtype-is-finite P H =
  has-decidable-equality-is-finite (is-finite-type-decidable-subtype P H)

has-decidable-equality-type-subset-Finite-Type :
  {l1 l2 : Level} (X : Finite-Type l1) (P : subset-Finite-Type l2 X) →
  has-decidable-equality (type-subset-Finite-Type X P)
has-decidable-equality-type-subset-Finite-Type X P =
  has-decidable-equality-is-finite (is-finite-type-subset-Finite-Type X P)
```

### The underlying type of a decidable subtype of a finite type is a set

```agda
is-set-type-subset-Finite-Type :
  {l1 l2 : Level} (X : Finite-Type l1) (P : subset-Finite-Type l2 X) →
  is-set (type-subset-Finite-Type X P)
is-set-type-subset-Finite-Type X P =
  is-set-type-decidable-subtype P (is-set-type-Finite-Type X)

set-subset-Finite-Type :
  {l1 l2 : Level} (X : Finite-Type l1) (P : subset-Finite-Type l2 X) →
  Set (l1 ⊔ l2)
set-subset-Finite-Type X P = set-decidable-subset (set-Finite-Type X) P
```

### The number of elements of a decidable subtype of a finite type is smaller than the number of elements of the ambient type

```agda
module _
  {l1 l2 : Level} (X : Finite-Type l1) (P : subset-Finite-Type l2 X)
  where

  number-of-elements-subset-Finite-Type : ℕ
  number-of-elements-subset-Finite-Type =
    number-of-elements-Finite-Type (finite-type-subset-Finite-Type X P)
```

### A subtype `S` over a type `A` with decidable equalities such that the underlying type generated by `S` is finite is a decidable subtype

```agda
is-decidable-subtype-is-finite-has-decidable-eq :
  {l1 l2 : Level} → {A : UU l1} → (S : subtype l2 A) →
  has-decidable-equality A → is-finite (type-subtype S) →
  is-decidable-subtype S
is-decidable-subtype-is-finite-has-decidable-eq S dec-A fin-S a =
  apply-universal-property-trunc-Prop
    ( fin-S)
    ( is-decidable-Prop (S a))
    ( λ count-S →
      rec-coproduct
        ( λ x → inl (tr (type-Prop ∘ S) (inv (pr2 x)) (pr2 (pr1 x))))
        ( λ x → inr λ S-a → x (( (a , S-a) , refl)))
        ( is-decidable-Σ-count count-S λ s → dec-A a (pr1 s)))
```

## References

{{#bibliography}}

## See also

- [Counting the elements of decidable subtypes](univalent-combinatorics.counting-decidable-subtypes.md)
