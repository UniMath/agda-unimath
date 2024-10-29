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
subset-𝔽 : {l1 : Level} (l2 : Level) → 𝔽 l1 → UU (l1 ⊔ lsuc l2)
subset-𝔽 l2 X = decidable-subtype l2 (type-𝔽 X)

module _
  {l1 l2 : Level} (X : 𝔽 l1) (P : subset-𝔽 l2 X)
  where

  subtype-subset-𝔽 : subtype l2 (type-𝔽 X)
  subtype-subset-𝔽 = subtype-decidable-subtype P

  is-decidable-subset-𝔽 : is-decidable-subtype subtype-subset-𝔽
  is-decidable-subset-𝔽 =
    is-decidable-decidable-subtype P

  is-in-subset-𝔽 : type-𝔽 X → UU l2
  is-in-subset-𝔽 = is-in-decidable-subtype P

  is-prop-is-in-subset-𝔽 :
    (x : type-𝔽 X) → is-prop (is-in-subset-𝔽 x)
  is-prop-is-in-subset-𝔽 = is-prop-is-in-decidable-subtype P
```

### The underlying type of a decidable subtype

```agda
module _
  {l1 l2 : Level} (X : 𝔽 l1) (P : subset-𝔽 l2 X)
  where

  type-subset-𝔽 : UU (l1 ⊔ l2)
  type-subset-𝔽 = type-decidable-subtype P

  inclusion-subset-𝔽 : type-subset-𝔽 → type-𝔽 X
  inclusion-subset-𝔽 = inclusion-decidable-subtype P

  is-emb-inclusion-subset-𝔽 : is-emb inclusion-subset-𝔽
  is-emb-inclusion-subset-𝔽 = is-emb-inclusion-decidable-subtype P

  is-injective-inclusion-subset-𝔽 : is-injective inclusion-subset-𝔽
  is-injective-inclusion-subset-𝔽 =
    is-injective-inclusion-decidable-subtype P

  emb-subset-𝔽 : type-subset-𝔽 ↪ type-𝔽 X
  emb-subset-𝔽 = emb-decidable-subtype P
```

## Properties

### The type of decidable subtypes of a finite type is finite

The computation of the number of subsets of a finite sets is the 52nd theorem on
[Freek Wiedijk's](http://www.cs.ru.nl/F.Wiedijk/) list of
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

Subset-𝔽 :
  {l1 : Level} (l2 : Level) → 𝔽 l1 → 𝔽 (l1 ⊔ lsuc l2)
pr1 (Subset-𝔽 l2 X) = subset-𝔽 l2 X
pr2 (Subset-𝔽 l2 X) = is-finite-decidable-subtype-is-finite (is-finite-type-𝔽 X)
```

### The type of decidable subsets of a finite type has decidable equality

```agda
has-decidable-equality-Subset-𝔽 :
  {l1 l2 : Level} (X : 𝔽 l1) →
  has-decidable-equality (decidable-subtype l2 (type-𝔽 X))
has-decidable-equality-Subset-𝔽 {l1} {l2} X =
  has-decidable-equality-is-finite
    ( is-finite-decidable-subtype-is-finite (is-finite-type-𝔽 X))
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

is-finite-type-subset-𝔽 :
  {l1 l2 : Level} (X : 𝔽 l1) (P : subset-𝔽 l2 X) →
  is-finite (type-subset-𝔽 X P)
is-finite-type-subset-𝔽 X P =
  is-finite-type-decidable-subtype P (is-finite-type-𝔽 X)

finite-type-subset-𝔽 :
  {l1 l2 : Level} (X : 𝔽 l1) → subset-𝔽 l2 X → 𝔽 (l1 ⊔ l2)
pr1 (finite-type-subset-𝔽 X P) = type-subset-𝔽 X P
pr2 (finite-type-subset-𝔽 X P) = is-finite-type-subset-𝔽 X P
```

### The underlying type of a decidable subtype has decidable equality

```agda
has-decidable-equality-type-decidable-subtype-is-finite :
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X) → is-finite X →
  has-decidable-equality (type-decidable-subtype P)
has-decidable-equality-type-decidable-subtype-is-finite P H =
  has-decidable-equality-is-finite (is-finite-type-decidable-subtype P H)

has-decidable-equality-type-subset-𝔽 :
  {l1 l2 : Level} (X : 𝔽 l1) (P : subset-𝔽 l2 X) →
  has-decidable-equality (type-subset-𝔽 X P)
has-decidable-equality-type-subset-𝔽 X P =
  has-decidable-equality-is-finite (is-finite-type-subset-𝔽 X P)
```

### The underlying type of a decidable subtype of a finite type is a set

```agda
is-set-type-subset-𝔽 :
  {l1 l2 : Level} (X : 𝔽 l1) (P : subset-𝔽 l2 X) → is-set (type-subset-𝔽 X P)
is-set-type-subset-𝔽 X P = is-set-type-decidable-subtype P (is-set-type-𝔽 X)

set-subset-𝔽 :
  {l1 l2 : Level} (X : 𝔽 l1) (P : subset-𝔽 l2 X) → Set (l1 ⊔ l2)
set-subset-𝔽 X P = set-decidable-subset (set-𝔽 X) P
```

### The number of elements of a decidable subtype of a finite type is smaller than the number of elements of the ambient type

```agda
module _
  {l1 l2 : Level} (X : 𝔽 l1) (P : subset-𝔽 l2 X)
  where

  number-of-elements-subset-𝔽 : ℕ
  number-of-elements-subset-𝔽 = number-of-elements-𝔽 (finite-type-subset-𝔽 X P)
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
