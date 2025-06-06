# Dirk Gently's principle

```agda
module logic.dirk-gentlys-principle where
```

<details><summary>Imports</summary>

```agda
open import foundation.disjunction
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Dirk Gently's principle" Agda=Dirk-Gently's-Principle}} is the
logical axiom that the type of [propositions](foundation-core.propositions.md)
is [linearly ordered](order-theory.total-orders.md). In other words, for every
pair of propositions `P` and `Q`, either `P` implies `Q` or `Q` implies `P`:

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
instance-prop-Dirk-Gently's-Principle :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
instance-prop-Dirk-Gently's-Principle P Q = (P ⇒ Q) ∨ (Q ⇒ P)

instance-Dirk-Gently's-Principle :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (l1 ⊔ l2)
instance-Dirk-Gently's-Principle P Q =
  type-Prop (instance-prop-Dirk-Gently's-Principle P Q)

Dirk-Gently's-Principle-Level : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Dirk-Gently's-Principle-Level l1 l2 =
  (P : Prop l1) (Q : Prop l2) → instance-Dirk-Gently's-Principle P Q

Dirk-Gently's-Principle : UUω
Dirk-Gently's-Principle =
  {l1 l2 : Level} → Dirk-Gently's-Principle-Level l1 l2
```

## Properties

### The law of excluded middle implies Dirk Gently's principle

**Proof.** Assuming the law of excluded middle, then every proposition is either
true or false, so since false ≤ true, we are done.

> This remains to be formalized.

## References

{{#bibliography}}

## External links

- This principle is studied under the name _Dummett's linearity axiom_ in
  [`Various.DummettDisjunction`](https://martinescardo.github.io/TypeTopology/Various.DummettDisjunction.html)
  at TypeTopology
