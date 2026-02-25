# Dirk Gently's principle

```agda
module logic.dirk-gentlys-principle where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.law-of-excluded-middle
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Dirk Gently's principle" Agda=Dirk-Gently-Principle}} is the logical
axiom that the type of [propositions](foundation-core.propositions.md) is
[linearly ordered](order-theory.total-orders.md). In other words, for every pair
of propositions `P` and `Q`, either `P` implies `Q` or `Q` implies `P`:

$$
  (P ⇒ Q) ∨ (Q ⇒ P).
$$

The proof strength of this principle lies strictly between the
[law of excluded middle](foundation.law-of-excluded-middle.md) and
[De Morgan's law](logic.de-morgans-law.md), Section 8.5 {{#cite Diener18}}.

> The name is based on the guiding principle of the protagonist of Douglas
> Adam’s novel Dirk Gently’s Holistic Detective Agency who believes in the
> “fundamental interconnectedness of all things.” {{#cite Diener18}}

## Statement

```agda
instance-prop-Dirk-Gently-Principle :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
instance-prop-Dirk-Gently-Principle P Q = (P ⇒ Q) ∨ (Q ⇒ P)

instance-Dirk-Gently-Principle :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (l1 ⊔ l2)
instance-Dirk-Gently-Principle P Q =
  type-Prop (instance-prop-Dirk-Gently-Principle P Q)

level-Dirk-Gently-Principle : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
level-Dirk-Gently-Principle l1 l2 =
  (P : Prop l1) (Q : Prop l2) → instance-Dirk-Gently-Principle P Q

Dirk-Gently-Principle : UUω
Dirk-Gently-Principle =
  {l1 l2 : Level} → level-Dirk-Gently-Principle l1 l2
```

## Properties

### The law of excluded middle implies Dirk Gently's principle

```agda
instance-Dirk-Gently-Principle-LEM' :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  is-decidable (type-Prop P) →
  instance-Dirk-Gently-Principle P Q
instance-Dirk-Gently-Principle-LEM' P Q (inl p) =
  inr-disjunction (λ _ → p)
instance-Dirk-Gently-Principle-LEM' P Q (inr np) =
  inl-disjunction (ex-falso ∘ np)

level-Dirk-Gently-Principle-LEM :
  (l1 l2 : Level) → level-LEM l1 → level-Dirk-Gently-Principle l1 l2
level-Dirk-Gently-Principle-LEM l1 l2 lem P Q =
  instance-Dirk-Gently-Principle-LEM' P Q (lem P)

level-Dirk-Gently-Principle-LEM' :
  (l1 l2 : Level) → level-LEM l2 → level-Dirk-Gently-Principle l1 l2
level-Dirk-Gently-Principle-LEM' l1 l2 lem P Q =
  swap-disjunction (level-Dirk-Gently-Principle-LEM l2 l1 lem Q P)
```

## References

{{#bibliography}}

## External links

- This principle is studied under the name _Dummett's linearity axiom_ in
  [`Various.DummettDisjunction`](https://martinescardo.github.io/TypeTopology/Various.DummettDisjunction.html)
  at TypeTopology
