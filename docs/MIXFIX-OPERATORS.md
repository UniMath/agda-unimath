# Mixfix operators in agda-unimath

This document outlines our choices of conventions for setting precedence levels
and associativity of
[mixfix operators in Agda](https://agda.readthedocs.io/en/latest/language/mixfix-operators.html),
and provides guidelines for this.

## Mixfix operators in Agda

Infix operators in Agda are binary operators that take arguments on either side.
For example, addition is commonly written in infix notation as `1 + 2`. Mixfix
operators are operators with longer names potentially containing multiple
components, where the arguments appear between the components. For example, the
commutator `[a,b]` is a common mixfix operator. The purpose of introducing infix
and mixfix operators in Agda is to make the code more readable by using commonly
accepted notation for widely used operators.

Mixfix operators can each be assigned a
[precedence level](https://agda.readthedocs.io/en/latest/language/mixfix-operators.html#precedence).
This can in principle be any signed fractional value, although we prefer them to
be nonnegative integral values. The higher this value is, the higher precedence
the operator has, meaning it is evaluated before operators with lower
precedence. By default in Agda, an operator is assigned a precedence level of
`20`.

For instance,
[multiplication on natural numbers `_*ℕ_`](elementary-number-theory.multiplication-natural-numbers.md)
is assigned the precedence level `40`, and
[addition on natural numbers `_+ℕ_`](elementary-number-theory.addition-natural-numbers.md)
is assigned the precedence level `35`. Therefore, the expression `x +ℕ y *ℕ z`
is parsed as `x +ℕ (y *ℕ z)`.

In addition to a precedence level, every infix operator can be defined to be
either left or right
[associative](https://agda.readthedocs.io/en/latest/language/mixfix-operators.html#associativity)
using the keywords `infixl` and `infixr`. It can be beneficial to define
associativity of operators to avoid excessively parenthesized expressions. The
parenthization should, however, never be omitted when this can make the code
more ambiguous or harder to read.

For instance, since the
[pairing operator `_,_`](foundation.dependent-pair-types.md) is defined to
associate to the right, the expression `a , b , c` is parsed as `a , (b , c)`.
By default, an operator does not associate to either side.

## Operator classes

We divide the different operators into broad classes, each assigned a range of
possible precedence levels. In broad terms, we discern between _parametric_ and
_nonparametric_ operators. The general rule is that nonparametric operator has
higher precedence than parametric operators. Parametric operators are operators
that take a universe level as one of their arguments. We consider an operator to
be parametric even if it only takes a universe level as an implicit argument.
Examples are the
[cartesian product type former`_×_`](foundation-core.cartesian-product-types.md),
the [identity type former `_＝_`](foundation-core.identity-types.md), and the
[pairing operator `_,_`](foundation.dependent-pair-types.md). Examples of
nonparametric operators are
[difference of integers `_-ℤ_`](elementary-number-theory.difference-integers.md),
[strict inequality on natural numbers `_<-ℕ_`](elementary-number-theory.strict-inequality-natural-numbers.md),
and
[multiplication of Eisenstein integers `_*ℤ[ω]_`](complex-numbers.eisenstein-integers.md).

Within these two classes, we make a further distinction between _relational_,
_additive_, _multiplicative_, _exponentiative_, and _unary_ operators, each with
a higher precedence than the previous one. All together, we assign ranges as
outlined below.

|                         | Relations | Additive | Multiplicative | Exponentiative | Unary |
| ----------------------- | --------- | -------- | -------------- | -------------- | ----- |
| Parametric Operators    | 5-9       | 10-14    | 15-19          | 20-24          | 25-29 |
| Nonparametric Operators | 30-34     | 35-39    | 40-44          | 45-49          | 50-54 |

Note that the default precedence level (`20`) falls within the range of
exponentiative parametric operators.

As a rule of thumb, the lowest value in a range is assigned by default. The
notable exceptions are outlined below.

## Special rules for assigning precedence levels

In this section, we outline special rules for assigning precedence levels to
particular classes of operators. Please make sure to update this section if new
rules are implemented.

### Function type like formation operators

In Agda, the arrow notation `_→_` for function type formation is directly
handled by the parser, hence it has hardcoded precedence and right
associativity. In particular, it has lower precedence than any user-declared
operator. To make other directed arrow notations like
[pointed function type formation `_→∗_`](structured-types.pointed-maps.md) and
[embedding type formation `_↪_`](foundation-core.embeddings.md) consistent with
this, we consider them as relational operators and assign them a precedence
level of `5`, and usually define them to be _right associative_. Other
relational operators are assigned the precedence level `6` by default.

### Pairing operators

The pairing operators [`_,_`](foundation.dependent-pair-types.md) and
[`_,ω_`](foundation.large-dependent-pair-types.md) are assigned a low precedence
level of `3`, below any of the above defined classes.

### Reasoning syntaxes

Reasoning syntaxes, like
[`equational-reasoning`](foundation-core.identity-types.md), is defined using
Agda's mixfix operators, and should have lower precedence than all other
operators (notably except for the built-in `_→_`). The precedence value range
`0-1` is reserved for these.

### Subtractive operators

We consider the class of subtractive operators as a subclass of additive
operators. These include operators like
[difference of integers `_-ℤ_`](elementary-number-theory.difference-integers.md).
Subtractive operators will usually have higher precedence than additive
operators, so that expressions like `a - b + c` are parsed as `(a - b) + c`.

## Assigning associativities

Below, we outline a list of general rules when assigning associativities.

- **Strictly associative operators**, e.g.
  [function composition `_∘_`](foundation-core.function-types.md), can be
  assigned _any associativity_.

- **Nonparametric arithmetic operators** are often naturally computed from left
  to right. For instance, the expression `1 - 2 - 3` is computed as
  `(1 - 2) - 3 = -1 - 3 = -4`, hence should be _left associative_. This applies
  to addition, subtraction, multiplication, and division. Note that for
  nonparametric exponentiation, we compute from right to left. I.e. `2 ^ 3 ^ 4`
  should compute as `2 ^ (3 ^ 4)`. Hence it will usually be _right associative_.

- **Arithmetic type formers** such as
  [coproduct type formation `_+_`](foundation-core.coproduct-types.md) and
  [cartesian product type formation `_×_`](foundation-core.cartesian-product-types.md),
  are natural to parse from left to right in terms of their
  introduction/elimination rules. Therefore, they are commonly associated to the
  _right_. This means that for instance to map into the left-hand argument of
  `A + B + C`, one uses a single `inl`.

- **Weakly associative operators**, meaning operators that are associative up to
  [identification](foundation-core.identity-types.md), may still be practical to
  define _an_ associativity for, for cases when the particular association does
  not matter and you still want to apply the operator multiple times. For
  instance, when performing an equality proof by a string of concatenations. For
  this reason, we define
  [identification concatenation `_∙_`](foundation-core.identity-types.md) and
  [homotopy concatenation `_∙h_`](foundation-core.homotopies.md) to be _left
  associative_. Please note that parenthization should still only be omitted
  when the association is of no importance, even if your expression is left
  associated regardless. For instance, one should never write

  ```agda
  assoc : p ∙ q ∙ r ＝ p ∙ (q ∙ r)
  ```

- **Unique well-typed associativity**. When an operator only has one well-typed
  associativity, then one can define it to have that associativity. For
  instance, with [homotopy left whiskering](foundation-core.homotopies.md),
  `f ·l g ·l H` is only ever well-typed when associated to the _right_.

## Full table of assigned precedences

| Precedence level | Operators                                                                                                                                                                                          |
| ---------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 50               | Unary nonparametric operators. This class is currently empty                                                                                                                                       |
| 45               | Exponentiative arithmetic operators                                                                                                                                                                |
| 40               | Multiplicative arithmetic operators                                                                                                                                                                |
| 36               | Subtractive arithmetic operators                                                                                                                                                                   |
| 35               | Additive arithmetic operators                                                                                                                                                                      |
| 30               | Relational arithmetic operators like`_≤-ℕ_` and `_<-ℕ_`                                                                                                                                            |
| 25               | Parametric unary operators like `¬_` and `¬¬_`                                                                                                                                                     |
| 20               | Parametric exponentiative operators. This class is currently empty                                                                                                                                 |
| 17               | Left homotopy whiskering `_·l_`                                                                                                                                                                    |
| 16               | Right homotopy whiskering `_·r_`                                                                                                                                                                   |
| 15               | Parametric multiplicative operators like `_×_`,`_×∗_`, `_∧_`, `_∧∗_`, `_*_`, function composition operators like `_∘_`,`_∘∗_`, `_∘e_`, and `_∘iff_`, concatenation operators like `_∙_` and `_∙h_` |
| 10               | Parametric additive operators like `_+_`, `_∨_`, `_∨∗_`, list concatenation, monadic bind operators for the type checking monad                                                                    |
| 6                | Parametric relational operators like `_＝_`, `_~_`, `_≃_`, `_⇔_`, and `_↔_`, elementhood relations, subtype relations                                                                             |
| 5                | Directed function type-like formation operators, e.g. `_⇒_`, `_↪_`, `_→∗_`, `_↠_`, `_↪ᵈ_`, and `_⊆_`                                                                                             |
| 3                | The pairing operators `_,_` and `_,ω_`                                                                                                                                                             |
| 0-1              | Reasoning syntaxes                                                                                                                                                                                 |
| -∞               | Function type formation `_→_`                                                                                                                                                                      |
