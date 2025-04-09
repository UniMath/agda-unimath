# The limited principle of omniscience

```agda
module foundation.limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.postcomposition-functions
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Statement

The
{{#concept "limited principle of omniscience" WDID=Q6549544 WD="limited principle of omniscience" Agda=LPO}}
(LPO) asserts that every [decidable subtype](foundation.decidable-subtypes.md)
of the [natural numbers](elementary-number-theory.natural-numbers.md) is
[merely decidable](foundation.decidable-types.md).

```agda
level-LPO-Prop : (l : Level) → Prop (lsuc l)
level-LPO-Prop l =
  Π-Prop
    ( decidable-subtype l ℕ)
    ( λ S → is-merely-decidable-Prop (type-decidable-subtype S))

level-LPO : (l : Level) → UU (lsuc l)
level-LPO l = type-Prop (level-LPO-Prop l)

LPO : UUω
LPO = {l : Level} → level-LPO l
```

## Properties

### Equivalent statement about booleans

```agda
has-true-or-all-false : (ℕ → bool) → UU lzero
has-true-or-all-false f =
  ( exists ℕ (λ n → is-true-Prop (f n))) +
  ( for-all ℕ (λ n → is-false-Prop (f n)))

has-true-or-all-false-Prop : (ℕ → bool) → Prop lzero
has-true-or-all-false-Prop f =
  ( has-true-or-all-false f ,
    is-prop-coproduct
      ( elim-exists
        ( ¬' ∀' ℕ (λ n → is-false-Prop (f n)))
        ( λ n t h → not-is-false-is-true (f n) t (h n)))
      ( is-prop-exists ℕ (λ n → is-true-Prop (f n)))
      ( is-prop-for-all-Prop ℕ (λ n → is-false-Prop (f n))))

bool-LPO-Prop : Prop lzero
bool-LPO-Prop = Π-Prop (ℕ → bool) (has-true-or-all-false-Prop)

bool-LPO : UU lzero
bool-LPO = type-Prop bool-LPO-Prop

opaque
  unfolding is-equiv-postcomp-is-equiv
  unfolding is-equiv-comp

  LPO-bool-LPO : bool-LPO → LPO
  LPO-bool-LPO blpo S =
    rec-coproduct
      ( elim-exists
        ( is-merely-decidable-Prop (type-decidable-subtype S))
        ( λ a fa → inl-disjunction (a , is-in-S a fa)))
      ( λ f~false →
        inr-disjunction
          ( λ (a , sa) →
            not-is-false-is-true (f a) (is-true-f a sa) (f~false a)))
      (blpo f)
    where
      f : ℕ → bool
      f = map-equiv (map-bool-decidable-subtype-equiv ℕ) S
      is-true-f : (n : ℕ) → is-in-decidable-subtype S n → f n ＝ true
      is-true-f n n∈S with S n
      ... | (_ , _ , inl n∈S') = refl
      ... | (_ , _ , inr n∉S') = ex-falso (n∉S' n∈S)
      is-in-S : (n : ℕ) → f n ＝ true → is-in-decidable-subtype S n
      is-in-S n fn with S n | fn
      ... | (_ , _ , inl n∈S) | _ = n∈S
      ... | (_ , _ , inr n∉S) | ()

  bool-LPO-level-LPO : {l : Level} → level-LPO l → bool-LPO
  bool-LPO-level-LPO {l} lpo f =
    elim-disjunction
      ( has-true-or-all-false-Prop f)
      ( λ (a , a∈S) → inl (intro-exists a (is-true-f a a∈S)))
      ( λ ¬fa → inr (λ a → is-false-f a (λ a∈S → ¬fa (a , a∈S))))
      ( lpo S)
    where
      S : decidable-subtype l ℕ
      S = map-inv-equiv (map-bool-decidable-subtype-equiv ℕ) f
      is-true-f : (n : ℕ) → is-in-decidable-subtype S n → f n ＝ true
      is-true-f n n∈S with f n | n∈S
      ... | true | _ = refl
      ... | false | map-raise ()
      is-false-f : (n : ℕ) → ¬ (is-in-decidable-subtype S n) → f n ＝ false
      is-false-f n n∉S with f n
      ... | true = ex-falso (n∉S (map-raise star))
      ... | false = refl

  level-LPO-iff-bool-LPO : (l : Level) → level-LPO l ↔ bool-LPO
  pr1 (level-LPO-iff-bool-LPO _) = bool-LPO-level-LPO
  pr2 (level-LPO-iff-bool-LPO l) blpo = LPO-bool-LPO blpo
```

### LPO at any universe level implies LPO for all universe levels

```agda
abstract
  LPO-level-LPO : {l : Level} → level-LPO l → LPO
  LPO-level-LPO level-lpo = LPO-bool-LPO (bool-LPO-level-LPO level-lpo)
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [Taboos.LPO](https://martinescardo.github.io/TypeTopology/Taboos.LPO.html) at
  TypeTopology
- [limited principle of omniscience](https://ncatlab.org/nlab/show/limited+principle+of+omniscience)
  at $n$Lab
