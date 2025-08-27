# The agda-unimath library style guide

The agda-unimath library is an ever-expanding encyclopedia of formalized
mathematics from a univalent point of view. The library's corresponding website
serves as an extensive platform, presenting our work in a structured,
encyclopedia-like format.

The coding and style conventions we've established aren't simply rules; they're
tools for us to shape and nurture this resource. They ensure that the formalized
definitions are clean and focused, and ready for reuse across the library,
thereby weaving each contribution into a bigger tapestry.

Conceptual clarity and readability are the core values of our formalization
project. This style guide aims to help contributors write code that is both
functional and understandable, as well as easily maintainable. Please reach out
to us if you have any questions or remarks about the agda-unimath style, or need
any help getting started with your formalization project. Our code, and also
this guide, are open to refinement to best support our community and the
project's goals.

## Code structuring conventions

The agda-unimath library is a comprehensive collection of formalized mathematics
spanning a broad range of subjects. All fields of mathematics are inherently
interlinked, which we leverage in our formalization process.

One critical aspect of maintaining such a large codebase lies in efficient and
strategic code structuring, and continued refactoring, into small, reusable
entries. In line with this approach, we aim to factor out and encapsulate even
the tiniest bits of reusable logic or computation in their own definitions.

Here are the benefits of this approach:

- **Simplicity**: Breaking down complex structures into smaller ones simplifies
  the overall codebase, making it more accessible to new contributors.

- **Reusability**: Once a particular logic or computation is formalized, it can
  be reused in multiple places, thereby avoiding redundancy and promoting
  efficiency.

- **Cleanliness**: By separating reusable logic from proof constructions, we
  keep our proofs clean and focus only on the essential parts of the argument.

- **Demonstrability**: Well-structured code serves as a practical guide on how
  to use prior parts of the library in the current setting or in new
  definitions.

- **Maintainability**: When logic is broken down into separate, reusable pieces,
  it becomes easier to manage and maintain the codebase. Constructions that are
  broken down into small definitions are much easier to understand. This also
  makes the project more scalable.

- **Reliability**: While formally verified code is guaranteed to be "correct" in
  terms of its internal logic, it doesn't necessarily ensure that a mathematical
  concept is accurately modeled within Agda. By proving properties, reusing
  existing implementations in manners that mirror the expectations of
  mathematicians, and by tightly integrating them with the rest of the library,
  we create more opportunities to use and confirm the fidelity of these
  implementations. This process bolsters confidence in their correctness and the
  overall reliability of the library.

In essence, our code structuring conventions are guided by the goal of ensuring
that our code remains as conceptually clear and as understandable as possible.
Finally, a maintainable codebase is a welcoming codebase. By ensuring that the
agda-unimath code is easy to understand and navigate, new contributors can more
readily participate in the project. This is crucial for the growth and dynamism
of the agda-unimath community. It allows a diverse group of developers, each
with their unique skills and perspectives, to contribute to the project's
ongoing success.

So, in particular, refactoring isn't just about "cleaning up" the code; it's a
strategic endeavor to ensure the longevity, vitality, and success of the
agda-unimath project.

## Guidelines for definitions in the agda-unimath library

- **Universe polymorphism**: We make use of universe polymorphism to make our
  definitions maximally applicable. Each assumed type or type family is assigned
  its own universe level.

- **Reuse of definitions**: We advocate for the reuse of existing constructions
  in both type specifications and definition bodies. This not only helps
  maintain naming consistency, but also highlights the correlation between
  current and prior definitions, while keeping our code concise and to the
  point.

- **Comprehensive infrastructure for key concepts**: To further elucidate the
  usage and scope of each concept in the library, we often invest in building
  comprehensive infrastructure around it. This approach not only clarifies the
  intent behind the definition but also helps keeping a consistent naming scheme
  by providing names for frequently used projections and other readily inferable
  definitions. The emphasis on infrastructure enhances the library's
  maintainability since modifications to well-supported definitions can be
  executed more easily than those lacking robust infrastructure. This is another
  way we endeavor to ensure the clarity, resilience, and continual evolution of
  our codebase. Good examples of files where infrastructure is well-developed
  include [`group-theory.groups`](group-theory.groups.md) and
  [`graph-theory.undirected-graphs`](graph-theory.undirected-graphs.md).

- **Implicit arguments**: If an argument can be inferred in most use cases, make
  it implicit.

- **Use of anonymous modules**: If several arguments are commonly used across
  different proofs, extract them into an anonymous module. This helps keep type
  specifications brief and ensures consistency in the variable ordering among
  related definitions.

- **Use of `where` blocks**: While `where` blocks are permissible, their use is
  generally discouraged as their content cannot be reused outside the main
  definition. This contradicts our objective of organizing the library into
  compact, reusable components. If a `where` block is deemed necessary, follow
  these conventions:

  - Opt for `where` blocks over `let` expressions.
  - Indent the `where` keyword by two spaces and align their content with the
    `where` keyword.
  - Position the `where` keyword on the line beneath the main proof, indented by
    two spaces.
  - Ensure each term has a type, and place all terms on lines following the
    `where` keyword. For instance:

  ```agda
  statement : Statement
  statement =
    some-possibly-long-proof a
    where
    a : type-of-a
    a = construction-of-a
  ```

- **Lambda expressions**: When a lambda expression appears as the argument of a
  function, we always wrap it in parentheses. We do this even if it is the last
  argument and thus isn't strictly required to be parenthesized. Note that in
  some rare cases, a lambda expression might appear at the top level. In this
  case we don't require the lambda expression to be parenthesized.

  There are multiple syntaxes for writing lambda expressions in Agda. Generally,
  you have the following options:

  1. Regular lambda expressions without pattern matching:

     ```agda
     λ x → x
     ```

  2. Pattern matching lambda expressions on record types:

     ```agda
     λ (x , y) → x
     ```

     This syntax only applies to record types with $η$-equality.

  3. Pattern matching lambda expressions with `{...}`:

     ```agda
     λ { (inl x) → ... ; (inr y) → ...}
     ```

  4. Pattern matching lambda expressions using the `where` keyword:

     ```agda
     λ where refl → refl
     ```

  All four syntaxes are in use in the library, although when possible we try to
  avoid general pattern matching lambdas, i.e. syntaxes 3 and 4. If need be, we
  prefer pattern matching using the `where` keyword over the `{...}` syntax.
  Note that whenever syntax 3 or 4 appear in as part of a construction, the
  definition should be marked as `abstract`. If computation is necessary for a
  definition that has these syntaxes in them, this suggests the relevant lambda
  expression(s) deserve to be factored out as separate definitions.

## Code comments

Given that the files in agda-unimath are literate Agda markdown files, designed
to be displayed in a user-friendly format on the agda-unimath website, we have
the opportunity to comment on our code using markdown outside of the code
blocks.

Each code block typically starts with a section header that provides a succinct
explanation of the code's purpose or functionality. This header can be followed
by a more detailed exposition of the code, elucidating the primary concepts and
methodologies used.

As an example, the page on
[joins of radical ideals](commutative-algebra.joins-radical-ideals-commutative-rings.md)
contains the following explanation of the code that is about to follow:

````md
### Products of radical ideals distribute over joins

Consider a radical ideal `I` and a family of radical ideals `J_α` indexed by
`α : U`. To prove distributivity, we make the following calculation where we
will write `·r` for the product of radical ideals and `⋁r` for the join of a
family of radical ideals.

```text
  I ·r (⋁r_α J_α) ＝ √ (I · √ (⋁_α J_α))
                  ＝ √ (I · (⋁_α J_α))
                  ＝ √ (⋁_α (I · J_α))
                  ＝ √ (⋁_α √ (I · J_α))
                  ＝ ⋁r_α (I ·r J_α)
```

The proof below proceeds by proving inclusions in both directions along the
computation steps above.

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  {U : UU l3} (J : U → radical-ideal-Commutative-Ring l4 A)
  where
```
````

The use of descriptive section headers, coupled with comprehensive markdown
explanations, allows readers to gain a conceptual understanding of the code's
purpose, and contributes towards making agda-unimath an informative resource of
formalized mathematics from a univalent point of view.

Note that in the process of writing comments for code, the question may come up
whether an anonymous module can extend across multiple code blocks and their
comments in between. This is indeed possible. We recommend, however, that
modules should not extend over markdown section headers of any level. The
sections and subsections in markdown are typically used to focus on a specific
definition, property, or example, and in this case it is good to start a new
anonymous module to display the context for the topic of that section.
Furthermore, it helps the maintainability of the library if modules don't extend
across too many code blocks.

Note that for consistency across the library, our convention is to use US
English in comments and other explanatory or introductory texts.

## Modules in the agda-unimath library

Modules play an important role in structuring Agda code. They allow us to group
related functions and definitions, increasing the readability and
maintainability of our codebase. Here are our guidelines for using modules in
the agda-unimath library:

- In Agda, every file should start by opening a module with the same name as the
  file. Generally, this should be the only named module in the file. Any
  additional modules should either be anonymous, or they should occur in the
  form of `record` or `data` definitions.

- However, we encourage the use of anonymous modules for grouping constructions
  that share a common theme or common parameters. Here is an example from
  [`graph-theory.directed-graphs`](graph-theory.directed-graphs.md):

  ```agda
  Directed-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
  Directed-Graph l1 l2 = Σ (UU l1) (λ V → V → V → UU l2)

  module _
    {l1 l2 : Level} (G : Directed-Graph l1 l2)
    where

    vertex-Directed-Graph : UU l1
    vertex-Directed-Graph = pr1 G

    edge-Directed-Graph : (x y : vertex-Directed-Graph) → UU l2
    edge-Directed-Graph = pr2 G
  ```

- We recommend leaving a single blank line after a module declaration for
  clarity and readability.

- Module variables should be declared on a new line, with an indentation level
  increase of two spaces. If the variables cannot fit on a single line, they can
  be declared over multiple lines.

- The `where` keyword should be positioned on a new line following the variable
  declarations, and it should also adopt the same two-space indentation level
  increase.

- If necessary, nested modules may be used. However, we recommend using them
  carefully and only when really needed. With nested modules it can sometimes be
  harder for readers as well as maintainers to keep track of assumptions.

- Module imports should occur directly after the file's named module declaration
  and should be listed in alphabetical order to simplify navigation. Note that
  our `pre-commit` hooks automatically organize the imports; the user does not
  need to sort them by hand.

- The library doesn't use
  [variables](https://agda.readthedocs.io/en/latest/language/generalization-of-declared-variables.html)
  at the moment. All variables are declared either as parameters of an anonymous
  module or in the type specification of a construction.

## Naming conventions

One of the key strategies to make our library easy to navigate is our naming
convention. We strive for a direct correspondence between a construction's name
and its type. Take, for instance, the proof that the successor function on
integers is an equivalence. It has the type `is-equiv succ-ℤ`, so we name it
`is-equiv-succ-ℤ`. Note how we prefer lowercase and use hyphens to separate
words.

We also reflect the type of hypotheses used in the construction within the name.
However, the crux of a name primarily describes the type of the constructed
term; descriptions of the hypotheses follow this. For instance,
`is-equiv-is-contr-map` is a function of type `is-contr-map f → is-equiv f`,
where `f` is a given function. Notice how the term `is-equiv-is-contr-map H`
places the descriptor `is-contr-map` right next to the variable `H` it refers
to.

While abbreviations might seem like a good way to shorten names, we use them
sparingly. They might save a couple of keystrokes for the author, but in the
grand scheme of things, they will likely compromise readability and
maintainability, especially for newcomers and maintainers. We aim for clarity,
not brevity.

Here is a list of our naming conventions:

- Names are unique; we steer clear of namespace overloading.

- Names should accurately convey the concept of its construction.

- We use US English spelling of words in names.

- Important concepts can be capitalized. Usually, these are categories like
  `Prop`, `Set`, `Semigroup`, `Monoid`, `Group`, `Preorder`, `Poset`,
  `Precategory`, `Category`, `Directed-Graph`, `Undirected-Graph`, and so on.

- As a general rule of thumb, names should start out with an all lowercase
  portion with words separated by hyphens, and may have a capitalized portion at
  the end that describes which larger mathematical framework the definition
  takes place in -- for instance, if it is constructed internally to a certain
  subuniverse or category of mathematical objects.

- The start of a name describes the object that is being constructed. For some
  theorems, the latter part of a name describes the hypotheses.

- Names never reference variables.

- We use Unicode symbols sparingly and only when they align with established
  mathematical practice.

- Just as we do with abbreviations, we use special symbols sparingly in names.

- If a symbol is not available, we describe the concept concisely in words.

- We prioritize the readability of the code and avoid subtly different
  variations of the same symbol. An important exception is the use of the
  [full width equals sign](https://codepoints.net/U+ff1d) for the identity type,
  as the standard equals sign is a reserved symbol in Agda.

## Formatting: indentation, line breaks, and parentheses { #formatting }

Code formatting is like punctuation in a novel - it helps readers make sense of
the story. Here's how we handle indentation and line breaks in the agda-unimath
library:

- In Agda, each definition is structured like a tree, where each operation can
  be seen as a branching point. We use indentation levels and parentheses to
  highlight this structure, which makes the code feel more organized and
  understandable. For example, when a definition part extends beyond a line, we
  introduce line breaks at the earliest branching point, clearly displaying the
  tree structure of the definition. This allows the reader to follow the
  branches of the tree, and to visually grasp the scope of each operation and
  argument. Consider the following example from
  [`foundation-core.truncated-types`](foundation-core.truncated-types.md):

  ```agda
  module _
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    where

    is-trunc-equiv-is-trunc :
      (k : 𝕋) → is-trunc k A → is-trunc k B → is-trunc k (A ≃ B)
    is-trunc-equiv-is-trunc k H K =
      is-trunc-Σ
        ( is-trunc-function-type k K)
        ( λ f →
          is-trunc-Σ
            ( is-trunc-Σ
              ( is-trunc-function-type k H)
              ( λ g →
                is-trunc-Π k (λ y → is-trunc-Id K (f (g y)) y)))
            ( λ _ →
              is-trunc-Σ
                ( is-trunc-function-type k H)
                ( λ h →
                  is-trunc-Π k (λ x → is-trunc-Id H (h (f x)) x))))
  ```

  The root here is the function `is-trunc-Σ`. It has two arguments, each
  starting on a fresh line with two extra spaces of indentation. The first
  argument fits neatly on one line, but the second one spills over. In these
  cases, we add a line break right after the `→` symbol following the
  lambda-abstraction, which is the earliest branching point in this case. The
  next node is again `is-trunc-Σ`, with two arguments. Neither of them fits on a
  line, so we add a line break immediately. This process is continued until the
  definition is complete.

  Note also that we use parentheses to mark the branches. The extra space after
  the opening parentheses marking a branch is there to visually emphasize the
  tree structure of the definition, and aligns well with our convention to have
  two-space indentation level increases.

- In order to improve the readability on the agda-unimath website, we use a
  standard line length of 80 characters. There are only a few exceptions that
  enable us to have names that are more than 80 characters long:

  - Named `module` declarations
  - `open import` statements
  - Lines consisting of a single, possibly parenthesized (`(){}`), token that is
    potentially followed by one of the symbols `;`, `:`, `=`, or `→`.

- The contents of a top-level module have zero indentation. For every subsequent
  nested scope, we add an extra two spaces of indentation, so the indentation
  level should always be a multiple of two.

- We always declare the variables of a module on a new line, with the
  indentation level increased by two spaces. If the variable declarations
  themselves spill over the 80 character line limit, we break them up with line
  breaks while grouping the variables together logically. The `where` keyword of
  a module declaration is entered on a new line after the variable declarations.

- If a construction's name and its type declaration do not fit into a single
  line, we move the type declaration to a new line with an extra two spaces of
  indentation. If the type specification still doesn't fit on an 80-character
  line, we break it up across lines, keeping the same indentation level.

- Some proofs contain a part with equational reasoning. The standard way to
  typeset equational reasoning proofs is as follows

  ```text
    equational-reasoning
      term-1
      ＝ term-2
        by
        equation-1
      ＝ term-3
        by
        equation-2
  ```

  Sometimes, however, `equation-n` is a short proof term that fits on the same
  line as `by` within the 80 character limit. In that case it is ok to do so.

- Expressions involving mixfix operators are appropriately parenthesized when
  the particular association bears relevance, or if there is any chance of
  confusion from omitting the parentheses. A reader of the code should not be
  expected to know the precedence levels or associativity of particular
  operators.

## Coding practices we tend to avoid

- Agda permits us to make quick definitions without specifying their types, but
  we avoid making such untyped definitions. While the type of the entry might be
  clear to you when you are writing the code, it puts a burden on the reader if
  you omit them. It is also hugely beneficial if you can see the specification
  of a certain entry by jumping to its definition. Furthermore, omitting
  specifications of entries might make maintenance a bit more difficult, because
  some name changes might still result in valid definitions, but with an
  unintended specifications. Catching such mistakes becomes a bit harder when
  you leave your entries untyped.

- Using Unicode characters in names is entirely permissible, but we recommend
  restraint to maintain readability. Just a few well-placed symbols can often
  express a lot.

- To enhance conceptual clarity, we suggest names of constructions avoid
  referring to variable names. This makes code more understandable, even at a
  glance, and easier to work with in subsequent code.

- We encourage limiting the depth increase of indentation levels to two spaces.
  This practice tends to keep our code reader-friendly, especially on smaller
  screens, by keeping more code on the left-hand side of the screen. In
  particular, we discourage the use of indentation for the sole purpose of
  aligning code to make it "neat". In our experience, this hurts the
  maintainability of the code, and you may find that it violates some of our
  other conventions as well.

- The use of `where` blocks in definitions is perfectly fine but keeping them
  short and specific to the definition of the current object is beneficial. Note
  that definitions made in a `where` block in a definition cannot be reused
  outside of that definition, and finding a way to factor out small lemmas into
  reusable definitions leads to more readable, maintainable, and also
  refactorable code. It can even help Agda's verification process run smoother.

- Record types aren't frequently used in the agda-unimath library. This is
  mostly because they make it more complex to characterize their identity type.
  However, when the identity type isn't as critical, feel free to use record
  types as they can be convenient.

- Using the projection functions `pr1` and `pr2`, particularly their
  compositions, can lead to short code, but we recommend to avoid doing so. When
  constructions contain a lot of projections throughout their definition, the
  projections reveal little of what is going on in that part of the projections.
  We therefore prefer naming the projections. When a type of the form `Σ A B` is
  given a name, naming its projections too can enhance readability and will
  provide more informative responses when jumping to the definition.
  Furthermore, it makes it easier to change the definition later on.

- Lastly, we recommend not naming constructions after infix notation of
  operations included in them. Preferring primary prefix notation over infix
  notation can help keep our code consistent. For example, it's preferred to use
  `commutative-product` instead of `commutative-×` for denoting the
  commutativity of cartesian products.

These guidelines are here to make everyone's coding experience more enjoyable
and productive. As always, your contributions to the agda-unimath library are
valued, and these suggestions are here to help ensure that your code is clear,
beautiful, reusable, and maintainable. Happy coding!
