# Mixfix operators in agda-unimath

This document outlines our choices of conventions for setting precedence levels
and associativity of
[mixfix operators in Agda](https://agda.readthedocs.io/en/v2.6.3.20230805/language/mixfix-operators.html),
and provides guidelines for this.

## Mixfix operators in Agda

Infix operations in Agda are binary operations that take arguments on either
side. For example, addition is commonly written in infix notation as `1 + 2`.
Mixfix operations are operations with longer names potentially containing
multiple components, where the arguments appear between the components. For
example, the commutator `[a,b]` is a common mixfix operation. The purpose of
introducing infix and mixfix operations in Agda is to make the code more
readable by using commonly accepted notation for widely used operations.

Mixfix operators can each be assigned a
[precedence level](https://agda.readthedocs.io/en/v2.6.3.20230805/language/mixfix-operators.html#precedence).
This can in principle be any signed fractional value, although we prefer them to
be non-negative integral values. The higher this value is, the higher precedence
the operator has, meaning it is evaluated before operators with lower
precedence. By default in Agda, an operator is assigned a precedence level of
`20`.

For instance, the operator `_*ℕ_` is assigned the precedence level `40`, and
`_+ℕ_` is assigned the precedence level `35`. Therefore, the expression
`x +ℕ y *ℕ z` is parsed as `x +ℕ (y *ℕ z)`.

In addition to a precedence level, every mixfix operator can be defined to be
either left or right
[associative](https://agda.readthedocs.io/en/v2.6.3.20230805/language/mixfix-operators.html#associativity).
It can be beneficial to define associativity of operators, to avoid excessively
parenthesized expressions. The parenthization should, however, never be omitted
when this can make the code more ambiguous or harder to read.

For instance, since the pairing operator `_,_` is defined to associate to the
right, the expression `a , b , c` is parsed as `a , (b , c)`. By default, an
operator does not associate to either side.

## Operator classes

We divide the different operators into broad classes, each assigned a range of
possible precedence levels. In broad terms, we discern between _parametric_ and
_non-parametric_ operators. The general rule is that non-parametric operator has
higher precedence than parametric operators. Parametric operators are operators
like the [cartesian product `_×_`](foundation-core.cartesian-product-types.md) ,
the [identity type former `_＝_`](foundation-core.identity-types.md) and the
[pairing operator `_,_`](foundation.dependent-pair-types.md). Examples of
non-parametric operators are
[`_-ℤ_`](elementary-number-theory.difference-integers.md)
[`_<-ℕ_`](elementary-number-theory.strict-inequality-natural-numbers.md) and
[`_*ℤ[ω]_`](commutative-algebra.eisenstein-integers.md).

Within these two classes, we make a further distinction between _relational_,
_additive_, _multiplicative_, _exponentiative_, and _unary_ operators, each with
a higher precedence than the previous one. All together, we assign ranges as
outlined below.

|                          | Relations | Additive | Multiplicative | Exponentiative | Unary |
| ------------------------ | --------- | -------- | -------------- | -------------- | ----- |
| Parametric Operations    | 5-9       | 10-14    | 15-19          | 20-24          | 25-29 |
| Nonparametric Operations | 30-34     | 35-39    | 40-44          | 45-49          | 50-54 |

Note that the default precedence level (`20`) falls within the range of
exponentiative parametric operations.

As a rule of thumb, the lowest value in a range is assigned by default. The
notable exceptions are outlined below.

## Special rules for assigning precedence levels

In this section, we outline special rules for assigning precedence levels to
particular classes of operations. Please make sure to update this section if new
rules are implemented.

### Function type like formation operations

In Agda, the arrow notation `_→_` for function type formation is directly
handled by the parser, hence it has hardcoded precedence and right
associativity. In particular, it has lower precedence than any user-declared
operator. To make other directed arrow notations like
[`_→∗_`](structured-types.pointed-maps.md) and
[`_↪_`](foundation-core.embeddings.md) consistent with this, we consider them as
relational operators and assign them the a precedence level of `5`, and usually
define them to be _right associative_. Other relational operators are assigned
the precedence level `6` by default.

### Reasoning syntax

Reasoning syntax, like
[`equational-reasoning`](foundation-core.identity-types.md), is defined using
Agda's mixfix operators, and should have lower precedence than all other
operators (notably except for `_→_`). The precedence value range `0-1` is
reserved for these.

### Subtractive operators

We consider the class of subtractive operators as a subclass of additive
operators. These include operators like
[`_-ℤ_`](elementary-number-theory.difference-integers.md) and . Subtractive
operators will usually have higher precedence than normal additive operators, so
that expressions like `a - b + c` are parsed as `(a - b) + c`.

## Assigning associativities

Below, we outline a list of general rules when assigning associativities.

- **Definitionally associative operators**, e.g. `_∘_`, can be assigned _any
  associativity_.
- **Non-parametric arithmetic operators** are often naturally computed from left
  to right. For instance, the expression `1 - 2 - 3` is computed as
  `(1 - 2) - 3 = -1 - 3 = -4`, hence should be _left associative_. This applies
  to addition, subtraction, multiplication and division. Note that for
  non-parametric exponentiation, we compute from right to left. I.e. `2 ^ 3 ^ 4`
  should compute as `2 ^ (3 ^ 4)`. Hence it will usually be _right associative_.
- **Arithmetic type formers** such as
  [`_+_`](foundation-core.coproduct-types.md) and
  [`_×_`](foundation-core.cartesian-product-types.md), are natural to parse from
  left to right in terms of their introduction/elimination rules. Therefore,
  they are commonly associated to the _right_. This means that for instance to
  map into the left hand argument of `A + B + C`, one uses a single `inl`.
- **Weakly associative operators**, meaning operators that are associative up to
  [identification](foundation-core.identity-types.md), may still be practical to
  define _an_ associativity for, for cases when the particular association does
  not matter and you still want to apply the operator multiple times. For
  instance, when performing an equality proof by a string of concatenations. For
  this reason, we define `_∙_` and `_∙h_` to be _left associative_. Please note
  that parenthization should still only be omitted when the association is
  completely irrelevant, even if your expression is left associated regardless.
  For instance, one should never write
  ```agda
  assoc : p ∙ (q ∙ r) ＝ p ∙ q ∙ r
  ```

## Full table of assigned precedences

| Precedence level | Operators                                                                                                                                                                                                                                    |
| ---------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 50               | Unary non-parametric operators. This class is currently empty                                                                                                                                                                                |
| 45               | Exponentiative arithmetic operators                                                                                                                                                                                                          |
| 40               | Multiplicative arithmetic operators                                                                                                                                                                                                          |
| 36               | Subtractive arithmetic operators                                                                                                                                                                                                             |
| 35               | Additive arithmetic operators                                                                                                                                                                                                                |
| 30               | Relational arithmetic operators, `_≤-ℕ_` and `_<-ℕ_`                                                                                                                                                                                         |
| 25               | Parametric unary operators. This class is currently empty                                                                                                                                                                                    |
| 20               | Parametric exponentiative operators. This class is currently empty                                                                                                                                                                           |
| 15               | Parametric multiplicative operators like `_×_`,`_×∗_`, `_∧_`, `_∧∗_`, function composition operations like `_∘_`,`_∘∗_`, `_∘e_`, and `_∘iff_`, identification concatenation and whiskering operations like `_∙_`, `_∙h_`, `_·l_`, and `_·r_` |
| 10               | Parametric additive operators like `_+_`, `_∨_`, `_∨∗_`, list concatenation, monadic bind operations for the type checking monad                                                                                                             |
| 6                | Parametric relational operations like `_＝_`, `_~_`, `_≃_`, and `_↔_`, elementhood relations, subtype relations                                                                                                                              |
| 5                | Directed function type-like formation operations, e.g. `_→∗_` and `_↪_`                                                                                                                                                                      |
| 3                | The pairing operations `_,_` and `_,ω_`                                                                                                                                                                                                      |
| 0-1              | Reasoning syntax                                                                                                                                                                                                                             |
| -∞               | Function type formation `_→_`                                                                                                                                                                                                                |
