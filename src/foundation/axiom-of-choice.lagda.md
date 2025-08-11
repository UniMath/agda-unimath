# The axiom of choice

```agda
module foundation.axiom-of-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.postcomposition-functions
open import foundation.projective-types
open import foundation.propositional-truncations
open import foundation.sections
open import foundation.split-surjective-maps
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.sets

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The {{#concept "axiom of choice" WD="axiom of choice" WDID=Q179692 Agda=AC0}}
asserts that for every family of [inhabited](foundation.inhabited-types.md)
types `B` indexed by a [set](foundation-core.sets.md) `A`, the type of sections
of that family `(x : A) → B x` is inhabited.

## Definition

### Instances of choice

```agda
instance-choice : {l1 l2 : Level} (A : UU l1) → (A → UU l2) → UU (l1 ⊔ l2)
instance-choice A B =
  ((x : A) → is-inhabited (B x)) → is-inhabited ((x : A) → B x)
```

Note that the above statement, were it true for all indexing types `A`, is
inconsistent with [univalence](foundation.univalence.md). For a concrete
counterexample see Lemma 3.8.5 in {{#cite UF13}}.

### The axiom of choice restricted to sets

```agda
instance-choice-Set :
  {l1 l2 : Level} (A : Set l1) → (type-Set A → Set l2) → UU (l1 ⊔ l2)
instance-choice-Set A B = instance-choice (type-Set A) (type-Set ∘ B)

level-AC-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
level-AC-Set l1 l2 =
  (A : Set l1) (B : type-Set A → Set l2) → instance-choice-Set A B

AC-Set : UUω
AC-Set = {l1 l2 : Level} → level-AC-Set l1 l2
```

### The axiom of choice

```agda
instance-choice₀ :
  {l1 l2 : Level} (A : Set l1) → (type-Set A → UU l2) → UU (l1 ⊔ l2)
instance-choice₀ A = instance-choice (type-Set A)

level-AC0 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
level-AC0 l1 l2 =
  (A : Set l1) (B : type-Set A → UU l2) → instance-choice₀ A B

AC0 : UUω
AC0 = {l1 l2 : Level} → level-AC0 l1 l2
```

## Properties

### Every type is set-projective if and only if the axiom of choice holds

```agda
is-set-projective-AC0 :
  {l1 l2 l3 : Level} → level-AC0 l2 (l1 ⊔ l2) →
  (X : UU l3) → is-set-projective l1 l2 X
is-set-projective-AC0 ac X A B f h =
  map-trunc-Prop
    ( ( map-Σ
        ( λ g → ((map-surjection f) ∘ g) ＝ h)
        ( precomp h A)
        ( λ s H → htpy-postcomp X H h)) ∘
      ( section-is-split-surjective (map-surjection f)))
    ( ac B (fiber (map-surjection f)) (is-surjective-map-surjection f))

AC0-is-set-projective :
  {l1 l2 : Level} →
  ({l : Level} (X : UU l) → is-set-projective (l1 ⊔ l2) l1 X) →
  level-AC0 l1 l2
AC0-is-set-projective H A B K =
  map-trunc-Prop
    ( map-equiv (equiv-Π-section-pr1 {B = B}) ∘ tot (λ g → htpy-eq))
    ( H ( type-Set A)
        ( Σ (type-Set A) B)
        ( A)
        ( pr1 , (λ a → map-trunc-Prop (map-inv-fiber-pr1 B a) (K a)))
        ( id))
```

## See also

- [Diaconescu's theorem](foundation.diaconescus-theorem.md), which states that
  the axiom of choice implies the law of excluded middle.
- [The axiom of countable choice](foundation.axiom-of-countable-choice.md), the
  axiom of choice restricted to [countable sets](set-theory.countable-sets.md).
- [The axiom of dependent choice](foundation.axiom-of-dependent-choice.md),
  another weaker form of the axiom of choice.
- [Finite choice](univalent-combinatorics.finite-choice.md), is the
  constructively true principle of the axiom of choice restricted to
  [finite types](univalent-combinatorics.finite-types.md).

## References

{{#bibliography}}
