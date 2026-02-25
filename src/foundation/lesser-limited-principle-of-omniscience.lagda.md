# The lesser limited principle of omniscience

```agda
module foundation.lesser-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.limited-principle-of-omniscience
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.transport-along-identifications
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

The {{#concept "lesser limited principle of omniscience" Agda=LLPO}} (LLPO)
asserts that if two [decidable subtypes](foundation.decidable-subtypes.md) of
the [natural numbers](elementary-number-theory.natural-numbers.md) are not
[both](foundation.conjunction.md) [inhabited](foundation.inhabited-subtypes.md),
then merely one [or](foundation.disjunction.md) the other are
[empty](foundation.empty-types.md).

## Definitions

### The small lesser limited principle of omniscience

```agda
level-prop-LLPO : (l : Level) → Prop (lsuc l)
level-prop-LLPO l =
  Π-Prop
    ( decidable-subtype l ℕ)
    ( λ A →
      Π-Prop
        ( decidable-subtype l ℕ)
        ( λ B →
          ¬'
            ( is-inhabited-decidable-subtype-Prop A ∧
              is-inhabited-decidable-subtype-Prop B) ⇒
          ( is-empty-decidable-subtype-Prop A ∨
            is-empty-decidable-subtype-Prop B)))

level-LLPO : (l : Level) → UU (lsuc l)
level-LLPO l = type-Prop (level-prop-LLPO l)

LLPO : UUω
LLPO = {l : Level} → level-LLPO l
```

## Properties

### The limited principle of omniscience implies the lesser limited principle of omniscience

```agda
level-LLPO-level-LPO : {l : Level} → level-LPO l → level-LLPO l
level-LLPO-level-LPO lpo A B ¬⟨A∧B⟩ =
  let
    motive =
      is-empty-decidable-subtype-Prop A ∨ is-empty-decidable-subtype-Prop B
  in
    elim-disjunction
      ( motive)
      ( λ inhabited-A →
        elim-disjunction
          ( motive)
          ( λ inhabited-B →
            ex-falso
              ( ¬⟨A∧B⟩
                ( unit-trunc-Prop inhabited-A , unit-trunc-Prop inhabited-B)))
          ( inr-disjunction)
          ( lpo B))
      ( inl-disjunction)
      ( lpo A)

LLPO-LPO : LPO → LLPO
LLPO-LPO lpo {l} = level-LLPO-level-LPO (lpo {l})
```

### Equivalent boolean formulation

```agda
bool-prop-LLPO : Prop lzero
bool-prop-LLPO =
  ∀'
  ( ℕ → bool)
  ( λ f →
    function-Prop
      ( is-prop (Σ ℕ (λ n → is-true (f n))))
      ( disjunction-Prop
        ( ∀' ℕ (λ n → function-Prop (is-even-ℕ n) (is-false-Prop (f n))))
        ( ∀' ℕ (λ n → function-Prop (is-odd-ℕ n) (is-false-Prop (f n))))))

bool-LLPO : UU lzero
bool-LLPO = type-Prop bool-prop-LLPO

abstract
  bool-LLPO-level-LLPO : {l : Level} → level-LLPO l → bool-LLPO
  bool-LLPO-level-LLPO {l} level-llpo f is-prop-true-f =
    elim-disjunction
      ( disjunction-Prop
          ( ∀' ℕ (λ n → function-Prop (is-even-ℕ n) (is-false-Prop (f n))))
          ( ∀' ℕ (λ n → function-Prop (is-odd-ℕ n) (is-false-Prop (f n)))))
      ( λ empty-A →
        inl-disjunction
          ( λ n (m , 2m=n) →
            tr (is-false ∘ f) 2m=n (false-f-empty-A empty-A m)))
      ( λ empty-B →
        inr-disjunction
          ( λ n odd-n →
            ind-Σ
              ( λ m 2m+1=n →
                tr (is-false ∘ f) 2m+1=n (false-f-empty-B empty-B m))
              ( has-odd-expansion-is-odd n odd-n)))
      ( level-llpo A B not-both-inhabited-A-B)
    where
      A B : decidable-subtype l ℕ
      A =
        raise-decidable-subtype l (λ n → is-true-decidable-subtype (f (n *ℕ 2)))
      B =
        raise-decidable-subtype
          ( l)
          ( λ n → is-true-decidable-subtype (f (succ-ℕ (n *ℕ 2))))
      f-2a-inhabitant-A :
        (n : ℕ) → is-in-decidable-subtype A n → f (n *ℕ 2) ＝ true
      f-2a-inhabitant-A _ = map-inv-raise
      f-2a+1-inhabitant-B :
        (n : ℕ) → is-in-decidable-subtype B n → f (succ-ℕ (n *ℕ 2)) ＝ true
      f-2a+1-inhabitant-B _ = map-inv-raise
      not-both-inhabited-A-B :
        ¬ (is-inhabited-decidable-subtype A × is-inhabited-decidable-subtype B)
      not-both-inhabited-A-B (inhabited-A , inhabited-B) =
        let
          open do-syntax-trunc-Prop empty-Prop
        in do
          (a , map-raise f2a) ← inhabited-A
          (b , map-raise f2b+1) ← inhabited-B
          noneq-odd-even
            ( succ-ℕ (b *ℕ 2))
            ( a *ℕ 2)
            ( is-odd-has-odd-expansion _ (b , refl))
            ( a , refl)
            ( ap
              ( pr1)
              ( eq-is-prop
                ( is-prop-true-f)
                { succ-ℕ (b *ℕ 2) , f2b+1}
                { a *ℕ 2 , f2a}))
      false-f-empty-A :
        is-empty-decidable-subtype A → (n : ℕ) → is-false (f (n *ℕ 2))
      false-f-empty-A ¬A n =
        is-false-is-not-true (f (n *ℕ 2)) (λ f2n → ¬A (n , map-raise f2n))
      false-f-empty-B :
        is-empty-decidable-subtype B → (n : ℕ) → is-false (f (succ-ℕ (n *ℕ 2)))
      false-f-empty-B ¬B n =
        is-false-is-not-true
          ( f _)
          ( λ f⟨2n+1⟩ → ¬B (n , map-raise f⟨2n+1⟩))
```

The reverse direction still needs a proof.

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [`Taboos.LLPO`](https://martinescardo.github.io/TypeTopology/Taboos.LLPO.html)
  at TypeTopology
- [lesser limited principle of omniscience](https://ncatlab.org/nlab/show/lesser+limited+principle+of+omniscience)
  at $n$Lab
